pub mod falcon;
mod lfold;
pub mod r1cs;
mod subring;

pub use lfold::{LFAcc, LFComp, LFVerifier};
pub use subring::{SplitRing, SplitRingPoly};

pub const FALCON_MOD: u128 = 12289;

/// Witness, signature vector components
#[derive(Clone, Debug)]
pub struct FalconSig {
    pub s1: Vec<u128>,
    pub s2: Vec<u128>,
}

/// Statement (public input)
#[derive(Clone, Debug)]
pub struct FalconInput {
    /// Public key
    pub h: Vec<u128>,
    /// Hash(r,m)
    pub c: Vec<u128>,
}

impl FalconSig {
    /// Calculate the l2-norms (squared) of the signature components.
    pub fn norms_squared(&self) -> (u128, u128) {
        let balance = |c: &u128| -> u128 {
            if *c > FALCON_MOD / 2 {
                FALCON_MOD - c
            } else {
                *c
            }
        };

        let s1_norm = self.s1.iter().map(balance).map(|c| c * c).sum::<u128>();
        let s2_norm = self.s2.iter().map(balance).map(|c| c * c).sum::<u128>();

        (s1_norm, s2_norm)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        SplitRing,
        falcon::deserialize,
        r1cs::{signature_verification_r1cs, signature_verification_splitring_z},
    };
    use anyhow::Result;
    use cyclotomic_rings::rings::{FrogChallengeSet as CS, FrogRingNTT as RqNTT};
    use falcon_rust::falcon512;
    use latticefold::{
        arith::{Arith, CCCS, CCS, Witness},
        commitment::AjtaiCommitmentScheme,
        decomposition_parameters::DecompositionParams,
    };
    use rand::Rng;

    #[derive(Clone)]
    pub struct DP {}
    impl DecompositionParams for DP {
        const B: u128 = 8388608;
        const L: usize = 3;
        const B_SMALL: usize = 2;
        const K: usize = 23;
    }

    const C: usize = 157;
    const W: usize = WIT_LEN * DP::L;
    const WIT_LEN: usize = 3260;
    type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;

    fn dummy_comp(ajtai: &Ajtai) -> Result<LFComp<RqNTT, C>> {
        let msg = b"Hello, world!";
        let (sk, pk) = falcon512::keygen(rand::thread_rng().r#gen());
        let sig = falcon512::sign(msg, &sk);

        let (x, w) = deserialize(msg, &sig, &pk);

        let d = 512;
        let k = 32;
        let log_bound = 26; // ceil(log2(34034726))

        let (r1cs, map) = signature_verification_r1cs::<SplitRing<RqNTT>>(1, k, d, log_bound);
        let z = signature_verification_splitring_z(&[(x, w)], log_bound, map)?;

        let x_len = r1cs.l;
        //println!("WIT_LEN: {}", z.len() - x_len - 1);
        r1cs.check_relation(&z)?;

        let ccs = CCS::from_r1cs_padded(r1cs, W, DP::L);
        ccs.check_relation(&z)?;

        let wit: Witness<RqNTT> = Witness::from_w_ccs::<DP>(z[x_len + 1..].to_vec());
        let cm_i = CCCS {
            cm: wit.commit::<C, W, DP>(ajtai)?,
            x_ccs: z[..x_len].to_vec(),
        };

        Ok(LFComp {
            witness: wit,
            cccs: cm_i,
            ccs,
        })
    }

    #[test]
    fn test_sig_fold() -> Result<()> {
        let mut rng = rand::thread_rng();

        let scheme = Ajtai::rand(&mut rng);
        let comp0 = dummy_comp(&scheme)?;
        let (mut agg, proof) = LFAcc::<RqNTT, DP, CS, C, W>::init(scheme, &comp0)?;
        let mut ctx = LFVerifier::<RqNTT, DP, CS, C>::init(&comp0, &proof)?;
        for _ in 0..3 {
            let comp = dummy_comp(agg.ajtai())?;
            let proof = agg.fold(&comp)?;
            ctx.verify(&comp, &proof)?;
        }

        Ok(())
    }
}
