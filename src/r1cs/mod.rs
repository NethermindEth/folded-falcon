mod builder;
mod ops;

pub use builder::R1CSBuilder;
pub use ops::{CSRing, Input};

use cyclotomic_rings::rings::SuitableRing;
use latticefold::arith::r1cs::{Constraint, ConstraintSystem, LinearCombination, R1CS};

pub fn signature_verification_r1cs<R: CSRing>(k: usize) -> R1CS<R::Base> {
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
    let norm_bound = R::cs_norm_bound(Input::private("s2"), 1, 4);

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
    use cyclotomic_rings::rings::FrogRingNTT as RqNTT;

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
    fn test_r1cs_signature_verification_w_bound() {
        // 1 + 2*3 = 7
        let r1cs = signature_verification_r1cs::<RqNTT>(0);
        // Variables
        // 0: h = 3
        // 1: c = 7
        // 2: s2 (norm) = 2
        // 3: 1
        // 4: s2 = 2
        // 5: s2*h = 6
        // 6: s1 = 1
        // 7: s2*h = 6
        // 8: s2 (norm) ^ 2 =  4
        // 9: norm = 4
        // 10..14 = binary decomp
        let z = &[
            RqNTT::from(3u32), // h
            RqNTT::from(7u32), // c
            RqNTT::from(2u32), // s2 [coeffs]
            RqNTT::from(1u32),
            RqNTT::from(2u32), // s2
            RqNTT::from(6u32), // s2*h
            RqNTT::from(1u32), // s1
            RqNTT::from(6u32), // s2*h
            RqNTT::from(4u32), // s2 [coeffs]^2
            RqNTT::from(4u32), // norm^2
            // binary decomp
            RqNTT::from(0u32),
            RqNTT::from(0u32),
            RqNTT::from(1u32),
            RqNTT::from(0u32),
        ];
        r1cs.check_relation(z).unwrap();
    }
}
