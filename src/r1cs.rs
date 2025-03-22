use cyclotomic_rings::rings::GoldilocksRingNTT;
use latticefold::arith::r1cs::{Constraint, ConstraintSystem, LinearCombination, R1CS};

type RqNTT = GoldilocksRingNTT;

pub fn signature_verification_r1cs() -> R1CS<RqNTT> {
    // s1 + s2*h = c
    let mut cs = ConstraintSystem::<RqNTT>::new();
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
    let a1 = LinearCombination::new().term(1u64, 4); // s2
    let b1 = LinearCombination::new().term(1u64, 1); // h
    let c1 = LinearCombination::new().term(1u64, 5); // s2*h
    cs.constraint(Constraint::new(a1, b1, c1));

    // Constraint 2: (s1 + s2h) * 1 = c
    let a2 = LinearCombination::new().term(1u64, 3).term(1u64, 5); // s1 + s2h
    let b2 = LinearCombination::new().term(1u64, 2); // 1
    let c2 = LinearCombination::new().term(1u64, 0); // c
    cs.constraint(Constraint::new(a2, b2, c2));

    cs.to_r1cs()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_r1cs_signature_verification() {
        let r1cs = signature_verification_r1cs();
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
}
