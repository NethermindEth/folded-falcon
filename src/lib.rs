mod falcon;
mod lfold;
pub mod r1cs;

pub use lfold::{LFAcc, LFComp, LFVerifier};

/// Witness, signature vector components
#[derive(Clone, Debug)]
pub struct FalconSig {
    pub s1: Vec<u8>,
    pub s2: Vec<u8>,
}

/// Statement (public input)
#[derive(Clone, Debug)]
pub struct FalconInput {
    /// Message
    pub msg: Vec<u8>,
    /// Public key
    pub h: Vec<u8>,
    /// Salt
    pub r: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use cyclotomic_rings::rings::GoldilocksRingNTT;
    use latticefold::{
        arith::{Arith, CCCS, CCS, Witness},
        commitment::AjtaiCommitmentScheme,
        decomposition_parameters::DecompositionParams,
    };
    #[derive(Clone)]
    pub struct DP {}
    impl DecompositionParams for DP {
        const B: u128 = 1 << 15;
        const L: usize = 5;
        const B_SMALL: usize = 2;
        const K: usize = 15;
    }
    const C: usize = 6;
    const W: usize = WIT_LEN * DP::L;
    const WIT_LEN: usize = 3;
    type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;
    type RqNTT = GoldilocksRingNTT;

    fn dummy_comp(ajtai: &Ajtai) -> LFComp<C> {
        let z = &[
            RqNTT::from(7u32),
            RqNTT::from(3u32),
            RqNTT::from(1u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(6u32),
        ];
        let ccs = CCS::from_r1cs_padded(r1cs::signature_verification_r1cs(), 2, DP::L);
        ccs.check_relation(z).expect("R1CS invalid!");

        let wit: Witness<RqNTT> = Witness::from_w_ccs::<DP>(vec![
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(6u32),
        ]);
        let cm_i = CCCS {
            cm: wit.commit::<C, W, DP>(ajtai).unwrap(),
            x_ccs: vec![RqNTT::from(7u32), RqNTT::from(3u32)],
        };

        LFComp {
            witness: wit,
            cccs: cm_i,
            ccs,
        }
    }

    #[test]
    fn test_sig_fold() {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::rand(&mut rng);
        let comp0 = dummy_comp(&scheme);
        let (mut agg, proof) = LFAcc::init(scheme, &comp0).unwrap();
        let mut ctx = LFVerifier::init(&comp0, &proof).unwrap();
        for _ in 0..3 {
            let comp = dummy_comp(agg.ajtai());
            let proof = agg.fold(&comp).unwrap();
            ctx.verify(&comp, &proof).unwrap();
        }
    }
}
