use anyhow::Result;
use cyclotomic_rings::rings::{GoldilocksChallengeSet, GoldilocksRingNTT};
use latticefold::{
    arith::{CCCS, CCS, LCCCS, Witness},
    commitment::AjtaiCommitmentScheme,
    decomposition_parameters::DecompositionParams,
    nifs::{
        LFProof, NIFSProver,
        linearization::{LFLinearizationProver, LinearizationProver},
    },
    transcript::poseidon::PoseidonTranscript,
};

// Parameters TODO move
#[derive(Clone)]
pub struct DP {}
impl DecompositionParams for DP {
    const B: u128 = 1 << 15;
    const L: usize = 5;
    const B_SMALL: usize = 2;
    const K: usize = 15;
}
type RqNTT = GoldilocksRingNTT;
type CS = GoldilocksChallengeSet;
type TS = PoseidonTranscript<RqNTT, CS>;
const C: usize = 8;
const W: usize = WIT_LEN * DP::L;
const WIT_LEN: usize = 4;
type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;

/// Signature TODO rename
#[derive(Clone, Debug)]
pub struct Sig {
    ccs: CCS<RqNTT>,
    cccs: CCCS<C, RqNTT>,
    witness: Witness<RqNTT>,
}

/// Accumulated signatures TODO rename
pub struct AggregatedSig {
    lcccs: LCCCS<C, RqNTT>,
    witness: Witness<RqNTT>,
    proof: LFProof<C, RqNTT>,
    transcript: TS,
    ajtai: AjtaiCommitmentScheme<C, W, RqNTT>,
    count: usize,
}

impl AggregatedSig {
    /// Initializes an aggregated signatures object from a single signature.
    pub fn init(ajtai: Ajtai, sig: &Sig) -> Result<Self> {
        let mut transcript = PoseidonTranscript::<RqNTT, CS>::default();

        // Linearize provided CCCS
        let (lcccs, _) = LFLinearizationProver::<_, PoseidonTranscript<RqNTT, CS>>::prove(
            &sig.cccs,
            &sig.witness,
            &mut transcript,
            &sig.ccs,
        )?;

        // Create initial running proof
        let (lcccs, witness, proof) = NIFSProver::<C, W, RqNTT, DP, TS>::prove(
            &lcccs,
            &sig.witness,
            &sig.cccs,
            &sig.witness,
            &mut transcript,
            &sig.ccs,
            &ajtai,
        )?;

        Ok(Self {
            lcccs,
            witness,
            proof,
            transcript,
            ajtai,
            count: 1,
        })
    }

    pub const fn ajtai(&self) -> &Ajtai {
        &self.ajtai
    }

    /// Add a signature
    pub fn fold(&mut self, sig: &Sig) -> Result<()> {
        let (lcccs, witness, proof) = NIFSProver::<C, W, RqNTT, DP, TS>::prove(
            &self.lcccs,
            &self.witness,
            &sig.cccs,
            &sig.witness,
            &mut self.transcript,
            &sig.ccs,
            &self.ajtai,
        )?;

        self.lcccs = lcccs;
        self.witness = witness;
        self.proof = proof;
        self.count += 1;

        Ok(())
    }

    /// Validate self
    pub fn verify(&self) -> Result<()> {
        // TODO
        Ok(())
    }

    /// Size of aggregated signatures over size of separate signatures
    pub fn compression_ratio(&self) -> f32 {
        // TODO self.serialize().len() / ( FalgonSig.serialize().len() * count )
        1.0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use latticefold::arith::{
        Arith, ccs::get_test_dummy_degree_three_ccs_non_scalar, r1cs::get_test_dummy_z_split_ntt,
    };

    const X_LEN: usize = 1;

    fn dummy_sig(ajtai: &Ajtai) -> Sig {
        let r1cs_rows = X_LEN + WIT_LEN + 1;

        let (one, x_ccs, w_ccs) = get_test_dummy_z_split_ntt::<RqNTT, X_LEN, WIT_LEN>();
        let mut z = vec![one];
        z.extend(&x_ccs);
        z.extend(&w_ccs);
        let ccs = get_test_dummy_degree_three_ccs_non_scalar::<RqNTT, X_LEN, WIT_LEN, W>(
            &z,
            DP::L,
            r1cs_rows,
        );
        ccs.check_relation(&z).expect("R1CS invalid!");

        let wit: Witness<RqNTT> = Witness::from_w_ccs::<DP>(w_ccs);
        let cm_i = CCCS {
            cm: wit.commit::<C, W, DP>(&ajtai).unwrap(),
            x_ccs,
        };

        Sig {
            witness: wit,
            cccs: cm_i,
            ccs,
        }
    }

    #[test]
    fn test_fold() -> Result<()> {
        let mut rng = rand::thread_rng();
        let scheme = Ajtai::rand(&mut rng);
        let sig = dummy_sig(&scheme);

        let mut agg = AggregatedSig::init(scheme, &sig)?;
        let sig = dummy_sig(&agg.ajtai());

        agg.fold(&sig)?;

        Ok(())
    }
}
