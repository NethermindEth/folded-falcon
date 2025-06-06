use anyhow::Result;
use ark_serialize::{CanonicalSerialize, Compress};
use cyclotomic_rings::{
    challenge_set::LatticefoldChallengeSet as ChallengeSet, rings::SuitableRing,
};
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
use std::marker::PhantomData;

type TS<R, CS> = PoseidonTranscript<R, CS>;
type Ajtai<R, const C: usize, const W: usize> = AjtaiCommitmentScheme<C, W, R>;

/// Single non-accumulated LatticeFold instance
#[derive(Clone, Debug)]
pub struct LFComp<R: SuitableRing, const C: usize> {
    /// Employed CCS
    pub ccs: CCS<R>,
    /// Committed CCS
    pub cccs: CCCS<C, R>,
    /// Un-committed witness
    pub witness: Witness<R>,
}

/// Single non-accumulated LatticeFold instance, without the witness
#[derive(Clone, Debug)]
pub struct LFCompVerifier<R: SuitableRing, const C: usize> {
    /// Employed CCS
    pub ccs: CCS<R>,
    /// Committed CCS
    pub cccs: CCCS<C, R>,
}

/// Accumulated LatticeFold instance
#[derive(Clone)]
pub struct LFAcc<
    R: SuitableRing,
    DP: DecompositionParams,
    CS: ChallengeSet<R>,
    const C: usize,
    const W: usize,
> {
    /// Linearized committed CCS
    pub lcccs: LCCCS<C, R>,
    /// Last used witness in the accumulated instance
    pub witness: Witness<R>,
    /// The current prover transcript
    pub transcript: TS<R, CS>,
    /// The employed Ajtai commitment matrix
    pub ajtai: Ajtai<R, C, W>,
    /// Number of folding calls
    pub count: usize,
    _dp: PhantomData<DP>,
}

/// LatticeFold Verifier context
#[derive(Clone)]
pub struct LFVerifier<R: SuitableRing, DP: DecompositionParams, CS: ChallengeSet<R>, const C: usize>
{
    transcript: TS<R, CS>,
    lcccs: LCCCS<C, R>,
    count: usize,
    _dp: PhantomData<DP>,
}

impl<R: SuitableRing, DP: DecompositionParams, CS: ChallengeSet<R>, const C: usize, const W: usize>
    LFAcc<R, DP, CS, C, W>
{
    /// Initializes an aggregated compnatures object from a single compnature.
    pub fn init(ajtai: Ajtai<R, C, W>, comp: &LFComp<R, C>) -> Result<(Self, LFProof<C, R>)> {
        let mut transcript = TS::<R, CS>::default();

        let lcccs = linearize::<_, CS, C>(comp)?;

        // Create initial running proof
        let (lcccs, witness, proof) = NIFSProver::<C, W, R, DP, TS<R, CS>>::prove(
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
                _dp: PhantomData,
            },
            proof,
        ))
    }

    /// Returns the employed Ajtai commitment matrix
    pub const fn ajtai(&self) -> &Ajtai<R, C, W> {
        &self.ajtai
    }

    /// Fold in a [`LFComp`] instance
    pub fn fold(&mut self, comp: &LFComp<R, C>) -> Result<LFProof<C, R>> {
        let (lcccs, witness, proof) = NIFSProver::<C, W, R, DP, TS<R, CS>>::prove(
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
}

impl<R: SuitableRing, DP: DecompositionParams, CS: ChallengeSet<R>, const C: usize>
    LFVerifier<R, DP, CS, C>
{
    /// Initialize the verifier context
    pub fn init(comp: &LFComp<R, C>, proof: &LFProof<C, R>) -> Result<Self> {
        let mut transcript = TS::<R, CS>::default();
        let lcccs = linearize::<R, CS, C>(comp)?;
        let lcccs = NIFSVerifier::<C, R, DP, TS<R, CS>>::verify(
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
            _dp: PhantomData,
        })
    }

    /// Verify some `proof` for the committed witness
    pub fn verify(&mut self, comp: &LFCompVerifier<R, C>, proof: &LFProof<C, R>) -> Result<()> {
        self.lcccs = NIFSVerifier::<C, R, DP, TS<R, CS>>::verify(
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

impl<R: SuitableRing, const C: usize> From<LFComp<R, C>> for LFCompVerifier<R, C> {
    fn from(comp: LFComp<R, C>) -> Self {
        LFCompVerifier {
            ccs: comp.ccs,
            cccs: comp.cccs,
        }
    }
}

fn linearize<R: SuitableRing, CS: ChallengeSet<R>, const C: usize>(
    comp: &LFComp<R, C>,
) -> Result<LCCCS<C, R>> {
    // Linearize provided CCCS
    Ok(LFLinearizationProver::<_, TS<R, CS>>::prove(
        &comp.cccs,
        &comp.witness,
        &mut TS::<R, CS>::default(),
        &comp.ccs,
    )?
    .0)
}

/// The compression ratio for some `proof` which is aggregating `n` Falcon signatures
///
/// Calculated using the size of the proof over the total size of the `n` signatures.
#[allow(clippy::cast_precision_loss)]
pub fn compression_ratio<const C: usize, R: SuitableRing>(n: usize, proof: &LFProof<C, R>) -> f64 {
    // TODO move, add 1024 deg support (1280 bytes)
    let sig_len: usize = 666;
    let salt_len: usize = 40;

    let mut serialized = Vec::new();
    proof
        .serialize_with_mode(&mut serialized, Compress::Yes)
        .unwrap();

    (serialized.len() + n * salt_len) as f64 / (n * (sig_len - salt_len)) as f64
}

#[cfg(test)]
mod tests {
    use super::*;
    use cyclotomic_rings::{rings::FrogChallengeSet as CS, rings::FrogRingNTT as RqNTT};
    use latticefold::arith::{
        Arith, ccs::get_test_dummy_degree_three_ccs_non_scalar, r1cs::get_test_dummy_z_split_ntt,
    };

    #[derive(Clone)]
    pub struct DP {}
    impl DecompositionParams for DP {
        const B: u128 = 8388608;
        const L: usize = 3;
        const B_SMALL: usize = 2;
        const K: usize = 23;
    }

    const C: usize = 8;
    const W: usize = WIT_LEN * DP::L;
    const WIT_LEN: usize = 8;
    const X_LEN: usize = 1;

    fn dummy_comp<R: SuitableRing>(ajtai: &Ajtai<R, C, W>) -> LFComp<R, C> {
        let r1cs_rows = X_LEN + WIT_LEN + 1;

        let (one, x_ccs, w_ccs) = get_test_dummy_z_split_ntt::<R, X_LEN, WIT_LEN>();
        let mut z = vec![one];
        z.extend(&x_ccs);
        z.extend(&w_ccs);
        let ccs = get_test_dummy_degree_three_ccs_non_scalar::<R, X_LEN, WIT_LEN, W>(
            &z,
            DP::L,
            r1cs_rows,
        );
        ccs.check_relation(&z).expect("R1CS invalid!");

        let wit: Witness<R> = Witness::from_w_ccs::<DP>(w_ccs);
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
        let comp0 = dummy_comp::<RqNTT>(&scheme);
        LFAcc::<RqNTT, DP, CS, C, W>::init(scheme, &comp0)?;

        Ok(())
    }

    #[test]
    fn test_multifold() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::<RqNTT, C, W>::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        let mut agg = LFAcc::<RqNTT, DP, CS, C, W>::init(scheme, &comp0)?.0;

        let comp1 = dummy_comp(agg.ajtai());
        agg.fold(&comp1)?;

        Ok(())
    }

    #[test]
    fn test_multifold_verify() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::<RqNTT, C, W>::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        let (mut agg, proof) = LFAcc::<RqNTT, DP, CS, C, W>::init(scheme.clone(), &comp0)?;
        let mut ctx = LFVerifier::<RqNTT, DP, CS, C>::init(&comp0, &proof)?;

        for _ in 0..3 {
            let comp = dummy_comp(agg.ajtai());
            let proof = agg.fold(&comp)?;
            ctx.verify(&comp.into(), &proof)?;
        }

        Ok(())
    }
}
