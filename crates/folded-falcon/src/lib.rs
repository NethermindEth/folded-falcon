//! # Falcon signature aggregation using LatticeFold
//!
//! A proof-of-concept signature aggregation scheme using [LatticeFold](https://github.com/NethermindEth/latticefold) to aggregate Falcon
//! signatures.
//!
//! ## Example
//! TODO
//!
//! ## Circuit
//! The main contribution of this crate is a low-level circuit (R1CS) containing the Falcon
//! signature verification method: $s_1 + s_2 h \stackrel{?}{=} c$, where $s_1$ and $s_2$ are
//! signature components, $h$ is the public key, and $c$ is the hash of the signature random salt
//! concatenated with the signed message.
//! Given we that we work with rings with a modulus $q$ much larger than the Falcon modulus $p =
//! 12289$, a lifting term $pv$ is also added to the main relation.
//!
//! Currently, the circuit in-use represents:
//! - the main relation: $s_1 + s_2 h + pv = c$;
//! - the $\ell^2$-norm bound check $(s_1, s_2) < \beta$, using an approximated bit-decomposition approach.
//!
//! ## Supported rings
//! Supported rings must implement the [`FoldedRing`] trait.
//! As of currently only the Frog ring configuration is supported for both Falcon variants
//! ([`config::F512Frog16`] and [`config::F1024Frog16`]).
//!
//! For polynomial rings with degree smaller $d'$ than the Falcon degree $d$ (512 or 1024), an homomorphism is provided
//! through the [`SplitRing`] type, where the Falcon polynomial is represented using smaller $k = d / d'$ subrings.

/// Usable ring configurations
pub mod config;
/// Falcon types and operations
pub mod falcon;
mod lfold;
/// The constraint system (R1CS)
pub mod r1cs;
mod subring;

pub use config::FoldedRing;
pub use lfold::{LFAcc, LFComp, LFVerifier, compression_ratio};
pub use subring::{SplitRing, SplitRingPoly};

use falcon::FalconPoly;

/// Witness, signature vector components
#[derive(Clone, Debug)]
pub struct FalconSig<const N: usize> {
    /// First component of the signature
    pub s1: FalconPoly<N>,
    /// Second component of the signature
    pub s2: FalconPoly<N>,
}

/// Statement (public input)
#[derive(Clone, Debug)]
pub struct FalconInput<const N: usize> {
    /// Public key
    pub h: FalconPoly<N>,
    /// Hash(r,m)
    pub c: FalconPoly<N>,
}

impl<const N: usize> FalconSig<N> {
    /// Calculate the l2-norms (squared) of the signature components.
    pub fn norms_squared(&self) -> (u64, u64) {
        (self.s1.norm_squared(), self.s2.norm_squared())
    }
}

#[cfg(feature = "slow-tests")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{config::F512Frog16 as FR, falcon::FalconOps};
    use anyhow::Result;
    use cyclotomic_rings::rings::{FrogChallengeSet as CS, FrogRingNTT as RqNTT};
    use latticefold::{
        arith::{Arith, CCCS, CCS, Witness},
        commitment::AjtaiCommitmentScheme,
        decomposition_parameters::DecompositionParams,
    };
    use rand::Rng;

    type Falcon = <FR as FoldedRing>::Variant;

    const C: usize = 38;
    const W: usize = WIT_LEN * DP::L;
    const WIT_LEN: usize = 3260;
    type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;

    #[derive(Clone)]
    pub struct DP {}
    impl DecompositionParams for DP {
        const B: u128 = 131072;
        const L: usize = 4;
        const B_SMALL: usize = 2;
        const K: usize = 17;
    }

    fn dummy_comp(ajtai: &Ajtai) -> Result<LFComp<RqNTT, C>> {
        let msg = b"Hello, world!";
        let (sk, pk) = Falcon::keygen(rand::thread_rng().r#gen());
        let sig = Falcon::sign(msg, &sk);

        let (x, w) = Falcon::deserialize(msg, &sig, &pk);

        let (r1cs, map) = FR::r1cs(1);
        let z = FR::z(&[(x, w)], map).unwrap();

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
            ctx.verify(&comp.into(), &proof)?;
        }

        Ok(())
    }
}
