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
    use crate::{SplitRing, SplitRingPoly, falcon::deserialize, lfold::DP, r1cs::ZBuilder};
    use anyhow::Result;
    use cyclotomic_rings::rings::{
        FrogChallengeSet as CS, FrogRingNTT as RqNTT, FrogRingPoly as RqPoly,
    };
    use falcon_rust::falcon512;
    use latticefold::{
        arith::{Arith, CCCS, CCS, Witness},
        commitment::AjtaiCommitmentScheme,
        decomposition_parameters::DecompositionParams,
    };
    use rand::Rng;
    use stark_rings::{PolyRing, Ring, cyclotomic_ring::CRT};

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

        let (r1cs, map) = r1cs::signature_verification_r1cs::<SplitRing<RqNTT>>(k, d, log_bound);

        let h_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&x.h).crt();
        let s2_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&w.s2).crt();
        let s1_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&w.s1).crt();
        let c_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&x.c).crt();
        let s2h = s2_r.clone() * h_r.clone();
        let s1ps2h = s1_r.clone() + s2h.clone();
        let v_r = s1ps2h.clone().icrt().lift(FALCON_MOD).crt();

        let s2h_cross = (0..k * k)
            .map(|idx| {
                let i = idx / k;
                let j = idx % k;
                let w = (i + j) / k;
                let mut x = RqPoly::ZERO;
                x.coeffs_mut()[w] = 1u32.into();
                s2_r.splits()[i] * h_r.splits()[j] * x.crt()
            })
            .collect::<Vec<_>>();

        let s1_p =
            w.s1.iter()
                .map(|c| {
                    let s = if *c > FALCON_MOD / 2 {
                        FALCON_MOD - *c
                    } else {
                        *c
                    };
                    RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(s))
                })
                .collect::<Vec<_>>();
        let s2_p =
            w.s2.iter()
                .map(|c| {
                    let s = if *c > FALCON_MOD / 2 {
                        FALCON_MOD - *c
                    } else {
                        *c
                    };
                    RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(s))
                })
                .collect::<Vec<_>>();

        let (s1_norm, s2_norm) = w.norms_squared();
        let norm = s1_norm + s2_norm;

        let mut remaining = norm;
        let mut norm_decomp = vec![RqNTT::from(0u32); log_bound];
        for (i, c) in norm_decomp.iter_mut().enumerate() {
            *c = if (remaining & (1 << i)) != 0 {
                remaining -= 1 << i;
                RqNTT::from(1u32)
            } else {
                RqNTT::from(0u32)
            };
        }

        let z = ZBuilder::<RqNTT>::new(map)
            .set("h", h_r.splits())?
            .set("c", c_r.splits())?
            .set("s1", s1_r.splits())?
            .set("s2", s2_r.splits())?
            .set("s2h", s2h.splits())?
            .set("s2*h", &s2h_cross)?
            .set("v", v_r.splits())?
            .set("s1+s2h", s1ps2h.splits())?
            .set("s1p", &s1_p)?
            .set("s2p", &s2_p)?
            .set("s1p*s1p", &s1_p.iter().map(|x| *x * *x).collect::<Vec<_>>())?
            .set("s2p*s2p", &s2_p.iter().map(|x| *x * *x).collect::<Vec<_>>())?
            .set("||s1p||^2", &[RqNTT::from(s1_norm)])?
            .set("||s2p||^2", &[RqNTT::from(s2_norm)])?
            .set("||s1p,s2p||^2 decomp", &norm_decomp)?
            .build()?;

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
        let (mut agg, proof) = LFAcc::<RqNTT, CS, C, W>::init(scheme, &comp0)?;
        let mut ctx = LFVerifier::<RqNTT, CS, C>::init(&comp0, &proof)?;
        for _ in 0..3 {
            let comp = dummy_comp(agg.ajtai())?;
            let proof = agg.fold(&comp)?;
            ctx.verify(&comp, &proof)?;
        }

        Ok(())
    }
}
