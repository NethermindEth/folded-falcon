mod builder;
mod ops;

pub use builder::{R1CSBuilder, ZBuildError, ZBuilder};
pub use ops::{CSRing, Input};

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
    // s1 + s2h = c
    let fin = R::cs_add(
        Input::private("s1"),
        Input::private("s2h"),
        Input::public("c"),
        k,
    );
    // norm bound
    let norm_bound =
        R::cs_norm_bound_xy(Input::private("s1p"), Input::private("s2p"), d, log_bound);

    builder.push(s2h);
    builder.push(fin);
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
    use crate::{SplitRing, SplitRingPoly};
    use anyhow::Result;
    use cyclotomic_rings::rings::{FrogRingNTT as RqNTT, FrogRingPoly as RqPoly};
    use stark_rings::PolyRing;

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
    fn test_r1cs_signature_verification_w_bound() -> Result<()> {
        // 1 + 2*3 = 7
        // ||s1||^2 + ||s2||^2 = 5 < 2^4
        let (r1cs, map) = signature_verification_r1cs::<RqNTT>(0, 1, 4);

        let z = ZBuilder::<RqNTT>::new(map)
            .set("h", &[3u32.into()])?
            .set("c", &[7u32.into()])?
            .set("s1", &[1u32.into()])?
            .set("s2", &[2u32.into()])?
            .set("s2h", &[6u32.into()])?
            .set("s1p", &[1u32.into()])?
            .set("s2p", &[2u32.into()])?
            .set("s1p*s1p", &[1u32.into()])?
            .set("s2p*s2p", &[4u32.into()])?
            .set("||s1p||^2", &[1u32.into()])?
            .set("||s2p||^2", &[4u32.into()])?
            .set(
                "||s1p,s2p||^2 decomp",
                &[1u32.into(), 0u32.into(), 1u32.into(), 0u32.into()],
            )? // Binary decomposition of 5 (total norm)
            .build()?;

        r1cs.check_relation(&z)?;

        Ok(())
    }

    #[test]
    fn test_r1cs_splitring_signature_verification_w_bound() -> Result<()> {
        let d = 512;
        let k = 32;
        let log_bound = 16;
        let (r1cs, map) = signature_verification_r1cs::<SplitRing<RqNTT>>(k, d, log_bound);

        // 20X^40 + 5X^10 * 5X^10 = 25X^20 + 20X^40
        let mut h = vec![0u128; 512];
        h[10] = 5;
        let mut s2 = vec![0u128; 512];
        s2[10] = 5;
        let mut s1 = vec![0u128; 512];
        s1[40] = 20;
        let mut c = vec![0u128; 512];
        c[20] = 25;
        c[40] = 20;

        let h_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&h).crt();
        let s2_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&s2).crt();
        let s1_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&s1).crt();
        let c_r: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&c).crt();
        let s2h_cross = &(0..32 * 32)
            .map(|idx| {
                let i = idx / 32;
                let j = idx % 32;
                s2_r.splits()[i] * h_r.splits()[j]
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

        let norm = s1.iter().map(|c| c * c).sum::<u128>() + s2.iter().map(|c| c * c).sum::<u128>();
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
            .set("||s1p||^2", &[RqNTT::from(400u32)])?
            .set("||s2p||^2", &[RqNTT::from(25u32)])?
            .set("||s1p,s2p||^2 decomp", &norm_decomp)?
            // Add cross-multiplication terms for s2*h
            .set("s2*h", s2h_cross)?
            .build()?;

        r1cs.check_relation(&z)?;

        Ok(())
    }
}
