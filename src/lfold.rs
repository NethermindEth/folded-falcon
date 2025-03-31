use anyhow::Result;
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

// Parameters TODO move
#[derive(Clone)]
pub struct DP {}
impl DecompositionParams for DP {
    const B: u128 = 1 << 15;
    const L: usize = 5;
    const B_SMALL: usize = 2;
    const K: usize = 15;
}
type TS<R, CS> = PoseidonTranscript<R, CS>;
type Ajtai<R, const C: usize, const W: usize> = AjtaiCommitmentScheme<C, W, R>;

/// Single non-accumulated LatticeFold instance
#[derive(Clone, Debug)]
pub struct LFComp<R: SuitableRing, const C: usize> {
    pub ccs: CCS<R>,
    pub cccs: CCCS<C, R>,
    pub witness: Witness<R>,
}

/// Accumulated LatticeFold instance
#[derive(Clone)]
pub struct LFAcc<R: SuitableRing, CS: ChallengeSet<R>, const C: usize, const W: usize> {
    pub lcccs: LCCCS<C, R>,
    pub witness: Witness<R>,
    pub transcript: TS<R, CS>,
    pub ajtai: Ajtai<R, C, W>,
    pub count: usize,
}

/// LatticeFold Verifier context
#[derive(Clone)]
pub struct LFVerifier<R: SuitableRing, CS: ChallengeSet<R>, const C: usize> {
    transcript: TS<R, CS>,
    lcccs: LCCCS<C, R>,
    count: usize,
}

impl<R: SuitableRing, CS: ChallengeSet<R>, const C: usize, const W: usize> LFAcc<R, CS, C, W> {
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
            },
            proof,
        ))
    }

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

    /// Size of aggregated compnatures over size of separate compnatures
    pub fn compression_ratio(&self) -> f32 {
        // TODO self.serialize().len() / ( FalgonSig.serialize().len() * count )
        1.0
    }
}

impl<R: SuitableRing, CS: ChallengeSet<R>, const C: usize> LFVerifier<R, CS, C> {
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
        })
    }

    pub fn verify(&mut self, comp: &LFComp<R, C>, proof: &LFProof<C, R>) -> Result<()> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use cyclotomic_rings::{rings::FrogChallengeSet as CS, rings::FrogRingNTT as RqNTT};
    use latticefold::arith::{
        Arith, ccs::get_test_dummy_degree_three_ccs_non_scalar, r1cs::get_test_dummy_z_split_ntt,
    };

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
        LFAcc::<RqNTT, CS, C, W>::init(scheme, &comp0)?;

        Ok(())
    }

    #[test]
    fn test_multifold() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::<RqNTT, C, W>::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        let mut agg = LFAcc::<RqNTT, CS, C, W>::init(scheme, &comp0)?.0;

        let comp1 = dummy_comp(agg.ajtai());
        agg.fold(&comp1)?;

        Ok(())
    }

    #[test]
    fn test_multifold_verify() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::<RqNTT, C, W>::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        let (mut agg, proof) = LFAcc::<RqNTT, CS, C, W>::init(scheme.clone(), &comp0)?;
        let mut ctx = LFVerifier::<RqNTT, CS, C>::init(&comp0, &proof)?;

        for _ in 0..3 {
            let comp = dummy_comp(agg.ajtai());
            let proof = agg.fold(&comp)?;
            ctx.verify(&comp, &proof)?;
        }

        Ok(())
    }
}
