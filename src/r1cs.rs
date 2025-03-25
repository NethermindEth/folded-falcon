use cyclotomic_rings::rings::FrogRingNTT;
use latticefold::arith::r1cs::{Constraint, ConstraintSystem, LinearCombination, R1CS};

type RqNTT = FrogRingNTT;

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
    let a1 = LinearCombination::new().add_term(1u64, 4); // s2
    let b1 = LinearCombination::new().add_term(1u64, 1); // h
    let c1 = LinearCombination::new().add_term(1u64, 5); // s2*h
    cs.add_constraint(Constraint::new(a1, b1, c1));

    // Constraint 2: (s1 + s2h) * 1 = c
    let a2 = LinearCombination::new().add_term(1u64, 3).add_term(1u64, 5); // s1 + s2h
    let b2 = LinearCombination::new().add_term(1u64, 2); // 1
    let c2 = LinearCombination::new().add_term(1u64, 0); // c
    cs.add_constraint(Constraint::new(a2, b2, c2));

    cs.to_r1cs()
}

pub fn splitring_mul_r1cs(k: usize) -> R1CS<RqNTT> {
    let mut cs = ConstraintSystem::<RqNTT>::new();

    // Variables:
    // 0..k-1: input s = [s_i]
    // k..2k-1: input s' = [s_j]
    // 2k: constant 1 (auxiliary input)
    // 2k+1..2k+k*k: auxiliary variables for cross-multiplications s_i*s_j
    // 2k+k*k+1..2k+k*k+k: output t_l
    cs.ninputs = 2 * k; // input polynomials s, s'
    cs.nauxs = k * k + k + 1; // k*k for cross-multiplications + k for outputs + constant 1

    // For each t_l
    for l in 0..k {
        // Multiplication constraints for each s_i*s_j
        for i in 0..k {
            for j in 0..k {
                if (i + j) % k == l {
                    let aux_idx = 2 * k + 1 + i * k + j;
                    let a = LinearCombination::single_term(1u64, i);
                    let b = LinearCombination::single_term(1u64, k + j);
                    let c = LinearCombination::single_term(1u64, aux_idx);
                    cs.add_constraint(Constraint::new(a, b, c));
                }
            }
        }

        // Addition constraint for the sum of s_i*s_j which composes t_l
        let mut sum_terms = Vec::new();
        for i in 0..k {
            for j in 0..k {
                if (i + j) % k == l {
                    let aux_idx = 2 * k + 1 + i * k + j;
                    sum_terms.push((1u64.into(), aux_idx));
                }
            }
        }
        let sum = LinearCombination::new().add_terms(&sum_terms);
        let output = LinearCombination::single_term(1u64, 2 * k + k * k + 1 + l);
        // sum * 1 = output
        cs.add_constraint(Constraint::new(
            sum,
            LinearCombination::single_term(1u64, 2 * k),
            output,
        ));
    }

    cs.to_r1cs()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SplitRing, SplitRingPoly};
    use cyclotomic_rings::rings::FrogRingPoly;
    type RqPoly = FrogRingPoly;

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

    #[test]
    fn test_r1cs_splitring_mul() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = splitring_mul_r1cs(k);

        // 5X^10 * 5X^10 = 25X^20
        let mut a_r = vec![0u128; 512];
        a_r[10] = 5;
        let mut b_r = vec![0u128; 512];
        b_r[10] = 5;

        let a: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&a_r).crt();
        let b: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&b_r).crt();
        let c: SplitRing<RqNTT> = a.clone() * b.clone();

        // Witness vector
        let z = {
            let mut z = Vec::with_capacity(2 * k + k * k + k + 1); // inputs + constant 1 + aux + output

            // input polys
            z.extend(a.splits());
            z.extend(b.splits());

            // constant 1
            z.push(RqNTT::from(1u32));

            // cross-multiplication terms s_i*s_j
            let mut aux_vars = vec![RqNTT::from(0u32); k * k];
            for i in 0..k {
                for j in 0..k {
                    let aux_idx = i * k + j;
                    aux_vars[aux_idx] = a[i] * b[j];
                }
            }
            z.extend(aux_vars.clone());

            // output poly t = [t_l]
            let mut t = vec![RqNTT::from(0u32); k];
            for l in 0..k {
                for i in 0..k {
                    for j in 0..k {
                        if (i + j) % k == l {
                            t[l] = t[l] + aux_vars[i * k + j];
                        }
                    }
                }
            }
            assert_eq!(t, c.splits()); // assert summation
            z.extend(t);

            z
        };

        r1cs.check_relation(&z).unwrap();
    }
}
