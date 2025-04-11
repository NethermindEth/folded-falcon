mod builder;
mod ops;

pub use builder::{R1CSBuilder, ZBuildError, ZBuilder};
pub use ops::{CSRing, Input};

use crate::FALCON_MOD;
use cyclotomic_rings::rings::SuitableRing;
use latticefold::arith::r1cs::{
    Constraint, ConstraintSystem, LinearCombination, R1CS, VariableMap,
};

pub fn signature_verification_r1cs<R: CSRing>(
    k: usize,
    d: usize,
    log_bound: usize,
) -> (R1CS<R::Base>, VariableMap) {
    let mut builder = R1CSBuilder::<R>::new();
    // s2*h
    let s2h = R::cs_mul(
        Input::private("s2"),
        Input::public("h"),
        Input::private("s2h"),
        k,
    );
    // s1 + s2h
    let fin = R::cs_add(
        Input::private("s1"),
        Input::private("s2h"),
        Input::private("s1+s2h"),
        k,
    );
    // s1 + s2h - pv = c
    let lift = R::cs_liftsub(
        Input::private("s1+s2h"),
        Input::private("v"),
        Input::public("c"),
        k,
        FALCON_MOD,
    );
    // norm bound
    let norm_bound =
        R::cs_norm_bound_xy(Input::private("s1p"), Input::private("s2p"), d, log_bound);

    builder.push(s2h);
    builder.push(fin);
    builder.push(lift);
    builder.push(norm_bound);

    builder.build()
}

pub fn signature_verification_cs<R: SuitableRing>() -> ConstraintSystem<R> {
    // s1 + s2*h = c
    let mut cs = ConstraintSystem::<R>::new();
    cs.ninputs = 2;
    cs.nauxs = 4;
    // Variables
    // 0: c = Hash(r, msg)
    // 1: h
    // 2: 1
    // 3: s1
    // 4: s2
    // 5: s2*h
    // Constraint 1: s2 * h = s2h
    let a1 = LinearCombination::new().add_term(1u64, 4); // s2
    let b1 = LinearCombination::new().add_term(1u64, 1); // h
    let c1 = LinearCombination::new().add_term(1u64, 5); // s2*h
    cs.add_constraint(Constraint::new(a1, b1, c1));

    // Constraint 2: (s1 + s2h) * 1 = c
    let a2 = LinearCombination::new().add_term(1u64, 3).add_term(1u64, 5); // s1 + s2h
    let b2 = LinearCombination::new().add_term(1u64, 2); // 1
    let c2 = LinearCombination::new().add_term(1u64, 0); // c
    cs.add_constraint(Constraint::new(a2, b2, c2));

    cs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SplitRing, SplitRingPoly, falcon::deserialize};
    use anyhow::Result;
    use cyclotomic_rings::rings::{FrogRingNTT as RqNTT, FrogRingPoly as RqPoly};
    use falcon_rust::falcon512;
    use rand::{Rng, thread_rng};
    use stark_rings::{PolyRing, Ring, cyclotomic_ring::CRT};

    #[test]
    fn test_r1cs_signature_verification() {
        let r1cs = signature_verification_cs().to_r1cs();
        // 1 + 2*3 = 7
        let z = &[
            RqNTT::from(7u32),
            RqNTT::from(3u32),
            RqNTT::from(1u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(6u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_signature_verification_0() -> Result<()> {
        let d = 512;
        let k = 32;
        let log_bound = 32;
        let (r1cs, map) = signature_verification_r1cs::<SplitRing<RqNTT>>(k, d, log_bound);

        // 20X^40 + 3000X^10 * 5X^10 = 2711^20 + 20X^40
        let mut h = vec![0u128; 512];
        h[10] = 5;
        let mut s2 = vec![0u128; 512];
        s2[10] = 3000;
        let mut s1 = vec![0u128; 512];
        s1[40] = 20;
        let mut c = vec![0u128; 512];
        c[20] = 2711;
        c[40] = 20;

        let h_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&h).crt();
        let s2_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&s2).crt();
        let s1_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&s1).crt();
        let c_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&c).crt();
        let s1ps2h: SplitRing<RqNTT> = s1_r.clone() + s2_r.clone() * h_r.clone();
        let v_r: SplitRing<RqNTT> = s1ps2h.clone().icrt().lift(FALCON_MOD).crt();
        let s2h_cross = &(0..k * k)
            .map(|idx| {
                let i = idx / k;
                let j = idx % k;
                let w = (i + j) / k;
                let mut x = RqPoly::ZERO;
                x.coeffs_mut()[w] = 1u32.into();
                s2_r.splits()[i] * h_r.splits()[j] * x.crt()
            })
            .collect::<Vec<_>>();

        let s1_p = s1
            .iter()
            .map(|c| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*c)))
            .collect::<Vec<_>>();
        let s2_p = s2
            .iter()
            .map(|c| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*c)))
            .collect::<Vec<_>>();

        let s1_norm = s1.iter().map(|c| c * c).sum::<u128>();
        let s2_norm = s2.iter().map(|c| c * c).sum::<u128>();
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
            .set("s2h", (h_r.clone() * s2_r.clone()).splits())?
            .set("s1p", &s1_p)?
            .set("s2p", &s2_p)?
            .set("s1p*s1p", &s1_p.iter().map(|x| *x * *x).collect::<Vec<_>>())?
            .set("s2p*s2p", &s2_p.iter().map(|x| *x * *x).collect::<Vec<_>>())?
            .set("||s1p||^2", &[RqNTT::from(s1_norm)])?
            .set("||s2p||^2", &[RqNTT::from(s2_norm)])?
            .set("||s1p,s2p||^2 decomp", &norm_decomp)?
            .set("s2*h", s2h_cross)?
            .set("v", v_r.splits())?
            .set("s1+s2h", s1ps2h.splits())?
            .build()?;

        r1cs.check_relation(&z)?;

        Ok(())
    }

    #[test]
    fn test_r1cs_splitring_signature_verification_falcon() -> Result<()> {
        let msg = b"Hello, world!";
        let (sk, pk) = falcon512::keygen(thread_rng().r#gen());
        let sig = falcon512::sign(msg, &sk);

        let (x, w) = deserialize(msg, &sig, &pk);

        let d = 512;
        let k = 32;
        let log_bound = 40;

        let (r1cs, map) = signature_verification_r1cs::<SplitRing<RqNTT>>(k, d, log_bound);

        let s1_r = SplitRingPoly::<RqPoly>::from_r(&w.s1).crt();
        let s2_r = SplitRingPoly::<RqPoly>::from_r(&w.s2).crt();
        let h_r = SplitRingPoly::<RqPoly>::from_r(&x.h).crt();
        let c_r = SplitRingPoly::<RqPoly>::from_r(&x.c).crt();

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
                .map(|c| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*c)))
                .collect::<Vec<_>>();
        let s2_p =
            w.s2.iter()
                .map(|c| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*c)))
                .collect::<Vec<_>>();

        let s1_norm = w.s1.iter().map(|c| c * c).sum::<u128>();
        let s2_norm = w.s2.iter().map(|c| c * c).sum::<u128>();
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

        r1cs.check_relation(&z)?;

        Ok(())
    }
}
