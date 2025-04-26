mod builder;
mod ops;

pub use builder::{R1CSBuilder, ZBuildError, ZBuilder};
pub use ops::{CSRing, Input, UnitMonomial};

use crate::{FALCON_MOD, FalconInput, FalconSig, SplitRingPoly};
use ark_ff::Field;
use cyclotomic_rings::rings::SuitableRing;
use latticefold::arith::r1cs::{
    Constraint, ConstraintSystem, LinearCombination, R1CS, VariableMap,
};
use stark_rings::{
    PolyRing, Ring, balanced_decomposition::convertible_ring::ConvertibleRing, cyclotomic_ring::CRT,
};

/// Falcon signature verification R1CS.
///
/// Arguments:
/// - `n` is the number of signatures per instance.
/// - `k` is the number of split rings, if a `SplitRing` is used in the constraint system.
/// - `d` is the degree of the original Falcon ring (512 or 1024).
/// - `log_bound` is the log-2 of the norm bound of the signature components $(s1, s2)$.
pub fn signature_verification_r1cs<R: CSRing>(
    n: usize,
    d: usize,
    log_bound: usize,
) -> (R1CS<R::Base>, VariableMap) {
    let mut builder = R1CSBuilder::<R>::new();

    for i in 0..n {
        // s2*h
        let s2h = R::cs_mul(
            Input::private(format!("{i}s2")),
            Input::public(format!("{i}h")),
            Input::private(format!("{i}s2{i}h")),
        );
        // s1 + s2h
        let fin = R::cs_add(
            Input::private(format!("{i}s1")),
            Input::private(format!("{i}s2{i}h")),
            Input::private(format!("{i}s1+{i}s2{i}h")),
        );
        // s1 + s2h - pv = c
        let lift = R::cs_liftsub(
            Input::private(format!("{i}s1+{i}s2{i}h")),
            Input::private(format!("{i}v")),
            Input::public(format!("{i}c")),
            FALCON_MOD.into(),
        );
        // norm bound
        let norm_bound = R::cs_norm_bound_xy(
            Input::private(format!("{i}s1p")),
            Input::private(format!("{i}s2p")),
            d,
            log_bound,
        );
        // coefficients used in norm bound are from s1, s2
        let combine_s1 = R::cs_combine(
            Input::private(format!("{i}s1")),
            Input::private(format!("{i}s1p")),
            d,
        );
        let combine_s2 = R::cs_combine(
            Input::private(format!("{i}s2")),
            Input::private(format!("{i}s2p")),
            d,
        );

        builder.push(s2h);
        builder.push(fin);
        builder.push(lift);
        builder.push(norm_bound);
        builder.push(combine_s1);
        builder.push(combine_s2);
    }

    builder.build()
}

pub fn signature_verification_splitring_z<R, const K: usize, const N: usize>(
    xw: &[(FalconInput<N>, FalconSig<N>)],
    log_bound: usize,
    map: VariableMap,
) -> Result<Vec<R>, ZBuildError>
where
    R: SuitableRing + UnitMonomial,
    <<R as stark_rings::PolyRing>::BaseRing as Field>::BasePrimeField: ConvertibleRing,
{
    let mut zbuild = ZBuilder::<R>::new(map);

    for (i, (x, w)) in xw.iter().enumerate() {
        let mut s1_srp = SplitRingPoly::<R::CoefficientRepresentation, K>::from_fpoly(&w.s1);
        s1_srp.center(FALCON_MOD);
        let s1_r = s1_srp.clone().crt();
        let mut s2_srp = SplitRingPoly::<R::CoefficientRepresentation, K>::from_fpoly(&w.s2);
        s2_srp.center(FALCON_MOD);
        let s2_r = s2_srp.clone().crt();
        let mut h_srp = SplitRingPoly::<R::CoefficientRepresentation, K>::from_fpoly(&x.h);
        h_srp.center(FALCON_MOD);
        let h_r = h_srp.crt();
        let c_r = SplitRingPoly::<R::CoefficientRepresentation, K>::from_fpoly(&x.c).crt();

        let s2h = s2_r.clone() * h_r.clone();
        let s1ps2h = s1_r.clone() + s2h.clone();
        let v_r = s1ps2h.clone().icrt().lift(FALCON_MOD).crt();

        let s2h_cross = (0..K * K)
            .map(|idx| {
                let i = idx / K;
                let j = idx % K;
                let w = (i + j) / K;
                let mut x = R::CoefficientRepresentation::ZERO;
                x.coeffs_mut()[w] = 1u32.into();
                s2_r.splits()[i] * h_r.splits()[j] * x.crt()
            })
            .collect::<Vec<_>>();

        let s1_p = s1_srp
            .recompose()
            .iter()
            .map(|c| R::from(*c))
            .collect::<Vec<_>>();
        let s2_p = s2_srp
            .recompose()
            .iter()
            .map(|c| R::from(*c))
            .collect::<Vec<_>>();

        let (s1_norm, s2_norm) = w.norms_squared();
        let norm = s1_norm + s2_norm;

        let mut remaining = norm;
        let mut norm_decomp = vec![R::from(0u32); log_bound];
        for (i, c) in norm_decomp.iter_mut().enumerate() {
            *c = if (remaining & (1 << i)) != 0 {
                remaining -= 1 << i;
                R::from(1u32)
            } else {
                R::from(0u32)
            };
        }

        zbuild
            .set(&format!("{i}h"), h_r.splits())?
            .set(&format!("{i}c"), c_r.splits())?
            .set(&format!("{i}s1"), s1_r.splits())?
            .set(&format!("{i}s2"), s2_r.splits())?
            .set(&format!("{i}s2{i}h"), s2h.splits())?
            .set(&format!("{i}s2*{i}h"), &s2h_cross)?
            .set(&format!("{i}v"), v_r.splits())?
            .set(&format!("{i}s1+{i}s2{i}h"), s1ps2h.splits())?
            .set(&format!("{i}s1p"), &s1_p)?
            .set(&format!("{i}s2p"), &s2_p)?
            .set(
                &format!("{i}s1p*{i}s1p"),
                &s1_p.iter().map(|x| *x * *x).collect::<Vec<_>>(),
            )?
            .set(
                &format!("{i}s2p*{i}s2p"),
                &s2_p.iter().map(|x| *x * *x).collect::<Vec<_>>(),
            )?
            .set(&format!("||{i}s1p||^2"), &[R::from(s1_norm)])?
            .set(&format!("||{i}s2p||^2"), &[R::from(s2_norm)])?
            .set(&format!("||{i}s1p,{i}s2p||^2 decomp"), &norm_decomp)?;
    }

    zbuild.build()
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
    use crate::{
        SplitRing,
        falcon::{Falcon512, FalconOps, FalconParams, FalconPoly, deserialize},
    };
    use cyclotomic_rings::rings::FrogRingNTT as RqNTT;
    use rand::{Rng, thread_rng};

    type Falcon = Falcon512;
    const K: usize = 32;
    type SplitNTT = SplitRing<RqNTT, K>;

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
    fn test_r1cs_splitring_signature_verification_dummy() {
        let (r1cs, map) = signature_verification_r1cs::<SplitNTT>(1, Falcon::N, Falcon::LSB2);

        // 20X^40 + 3000X^10 * 5X^10 = 2711^20 + 20X^40
        let mut h = FalconPoly::<{ Falcon::N }>::new();
        h.coeffs_mut()[10] = 5;
        let mut s2 = FalconPoly::new();
        s2.coeffs_mut()[10] = 3000;
        let mut s1 = FalconPoly::new();
        s1.coeffs_mut()[40] = 20;
        let mut c = FalconPoly::new();
        c.coeffs_mut()[20] = 2711;
        c.coeffs_mut()[40] = 20;

        let x = FalconInput { h, c };
        let w = FalconSig { s1, s2 };

        let z =
            signature_verification_splitring_z::<_, K, { Falcon::N }>(&[(x, w)], Falcon::LSB2, map)
                .unwrap();
        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_signature_verification_falcon() {
        let msg = b"Hello, world!";
        let (sk, pk) = Falcon::keygen(thread_rng().r#gen());
        let sig = Falcon::sign(msg, &sk);

        let (x, w) = deserialize(msg, &sig, &pk);

        let (r1cs, map) = signature_verification_r1cs::<SplitNTT>(1, Falcon::N, Falcon::LSB2);
        let z =
            signature_verification_splitring_z::<_, K, { Falcon::N }>(&[(x, w)], Falcon::LSB2, map)
                .unwrap();
        r1cs.check_relation(&z).unwrap();
    }
}
