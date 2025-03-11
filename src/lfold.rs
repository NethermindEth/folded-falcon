use anyhow::Result;
use cyclotomic_rings::rings::{GoldilocksChallengeSet, GoldilocksRingNTT};
use latticefold::{
    arith::{CCCS, CCS, LCCCS, Witness},
    commitment::AjtaiCommitmentScheme,
    decomposition_parameters::DecompositionParams,
    nifs::{
        LFProof, NIFSProver, NIFSVerifier,
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
const WIT_LEN: usize = 8;
type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;

/// Single non-accumulated LatticeFold instance
#[derive(Clone, Debug)]
pub struct LFComp {
    ccs: CCS<RqNTT>,
    cccs: CCCS<C, RqNTT>,
    witness: Witness<RqNTT>,
}

/// Accumulated LatticeFold instance
#[derive(Clone)]
pub struct LFAcc {
    lcccs: LCCCS<C, RqNTT>,
    witness: Witness<RqNTT>,
    transcript: TS,
    ajtai: AjtaiCommitmentScheme<C, W, RqNTT>,
    count: usize,
}

/// LatticeFold Verifier context
#[derive(Clone)]
pub struct LFVerifier {
    transcript: TS,
    lcccs: LCCCS<C, RqNTT>,
    count: usize,
}

impl LFAcc {
    /// Initializes an aggregated compnatures object from a single compnature.
    pub fn init(ajtai: Ajtai, comp: &LFComp) -> Result<(Self, LFProof<C, RqNTT>)> {
        let mut transcript = TS::default();

        let lcccs = linearize(comp)?;

        // Create initial running proof
        let (lcccs, witness, proof) = NIFSProver::<C, W, RqNTT, DP, TS>::prove(
            &lcccs,
            &comp.witness,
            &comp.cccs,
            &comp.witness,
            &mut transcript,
            &comp.ccs,
            &ajtai,
        )?;

        Ok((
            Self {
                lcccs,
                witness,
                transcript,
                ajtai,
                count: 1,
            },
            proof,
        ))
    }

    pub const fn ajtai(&self) -> &Ajtai {
        &self.ajtai
    }

    /// Fold in a [`LFComp`] instance
    pub fn fold(&mut self, comp: &LFComp) -> Result<LFProof<C, RqNTT>> {
        let (lcccs, witness, proof) = NIFSProver::<C, W, RqNTT, DP, TS>::prove(
            &self.lcccs,
            &self.witness,
            &comp.cccs,
            &comp.witness,
            &mut self.transcript,
            &comp.ccs,
            &self.ajtai,
        )?;

        self.lcccs = lcccs;
        self.witness = witness;
        self.count += 1;

        Ok(proof)
    }

    /// Size of aggregated compnatures over size of separate compnatures
    pub fn compression_ratio(&self) -> f32 {
        // TODO self.serialize().len() / ( FalgonSig.serialize().len() * count )
        1.0
    }
}

impl LFVerifier {
    pub fn init(comp: &LFComp, proof: &LFProof<C, RqNTT>) -> Result<Self> {
        let mut transcript = TS::default();
        let lcccs = linearize(comp)?;
        let lcccs = NIFSVerifier::<C, RqNTT, DP, TS>::verify(
            &lcccs,
            &comp.cccs,
            proof,
            &mut transcript,
            &comp.ccs,
        )?;

        Ok(Self {
            transcript,
            lcccs,
            count: 1,
        })
    }

    pub fn verify(&mut self, comp: &LFComp, proof: &LFProof<C, RqNTT>) -> Result<()> {
        self.lcccs = NIFSVerifier::<C, RqNTT, DP, TS>::verify(
            &self.lcccs,
            &comp.cccs,
            proof,
            &mut self.transcript,
            &comp.ccs,
        )?;
        self.count += 1;

        Ok(())
    }
}

fn linearize(comp: &LFComp) -> Result<LCCCS<C, RqNTT>> {
    // Linearize provided CCCS
    Ok(LFLinearizationProver::<_, TS>::prove(
        &comp.cccs,
        &comp.witness,
        &mut TS::default(),
        &comp.ccs,
    )?
    .0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use latticefold::arith::{
        Arith, ccs::get_test_dummy_degree_three_ccs_non_scalar, r1cs::get_test_dummy_z_split_ntt,
    };

    const X_LEN: usize = 1;

    fn dummy_comp(ajtai: &Ajtai) -> LFComp {
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
            cm: wit.commit::<C, W, DP>(ajtai).unwrap(),
            x_ccs,
        };

        LFComp {
            witness: wit,
            cccs: cm_i,
            ccs,
        }
    }

    #[test]
    fn test_fold() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        LFAcc::init(scheme, &comp0)?;

        Ok(())
    }

    #[test]
    fn test_multifold() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        let mut agg = LFAcc::init(scheme, &comp0)?.0;

        let comp1 = dummy_comp(agg.ajtai());
        agg.fold(&comp1)?;

        Ok(())
    }

    #[test]
    fn test_multifold_verify() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        let (mut agg, proof) = LFAcc::init(scheme.clone(), &comp0)?;
        let mut ctx = LFVerifier::init(&comp0, &proof)?;

        for _ in 0..3 {
            let comp = dummy_comp(agg.ajtai());
            let proof = agg.fold(&comp)?;
            ctx.verify(&comp, &proof)?;
        }

        Ok(())
    }
}
