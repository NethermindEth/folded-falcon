use super::SplitRing;
use cyclotomic_rings::rings::SuitableRing;
use latticefold::arith::r1cs::{Constraint, ConstraintSystem, LinearCombination, R1CS};
use stark_rings_linalg::SparseMatrix;
use std::cmp::Ordering;

pub trait CSRing {
    type Base: SuitableRing;

    /// Multiplication constraint system for rings, `s * sp = t`.
    /// `k` is the number of splits for a [`SplitRing`]
    fn cs_mul(s: Input, sp: Input, t: Input, k: usize) -> ConstraintSystem<Self::Base>;

    /// CS with l2- norm calculation, norm bound constraints, for some poly of degree `d`.
    /// `log_bound` must be the log2 of the norm bound. Only powers of 2 bounds are currently supported.
    /// The norm is constrained to be representable with only `log_bound` bits.
    fn cs_norm_bound(d: usize, log_bound: usize) -> ConstraintSystem<Self::Base>;
}

impl<R: SuitableRing> CSRing for SplitRing<R> {
    type Base = R;

    fn cs_mul(s: Input, sp: Input, t: Input, k: usize) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        // Variables (one witness ring):
        // 0..k: public ring
        // k..2k: public ring
        // 2k: constant 1
        // 2k+1..3k+1: private ring
        // 3k+1..3k+1+k*k: auxiliary variables for cross-multiplications

        // Variables (two witness rings):
        // 0..k: public ring
        // k: constant 1
        // k+1..2k+1: private ring
        // 2k+1..3k+1: private ring
        // 3k+1..3k+1+k*k: auxiliary variables for cross-multiplications

        let (s_index, sp_index, t_index, one_index) = match (s, sp, t) {
            (Input::Public, Input::Public, Input::Private) => (0, k, 2 * k + 1, 2 * k),
            (Input::Private, Input::Private, Input::Public) => (k + 1, 2 * k + 1, 0, k),
            (Input::Public, Input::Private, Input::Public)
            | (Input::Private, Input::Public, Input::Public) => (0, 2 * k + 1, k, 2 * k),
            (Input::Public, Input::Private, Input::Private)
            | (Input::Private, Input::Public, Input::Private) => (0, k + 1, 2 * k + 1, k),
            _ => panic!("{s:?} * {sp:?} = {t:?} relation not supported"),
        };

        let nvars = k + k + k + 1 + k * k;
        let aux_index = 3 * k + 1;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // For each t_l
        for l in 0..k {
            // Multiplication constraints for each s_i*s'_j
            for i in 0..k {
                for j in 0..k {
                    if (i + j) % k == l {
                        let aux_idx = aux_index + i * k + j;
                        let a = LinearCombination::single_term(1u64, s_index + i);
                        let b = LinearCombination::single_term(1u64, sp_index + j);
                        let c = LinearCombination::single_term(1u64, aux_idx);
                        cs.add_constraint(Constraint::new(a, b, c));
                    }
                }
            }

            // Addition constraint for the sum of s_i*s'_j which composes t_l
            let mut sum_terms = Vec::new();
            for i in 0..k {
                for j in 0..k {
                    if (i + j) % k == l {
                        let aux_idx = aux_index + i * k + j;
                        sum_terms.push((1u64.into(), aux_idx));
                    }
                }
            }
            let sum = LinearCombination::new().add_terms(&sum_terms);
            let output = LinearCombination::single_term(1u64, t_index + l);
            // sum * 1 = output
            cs.add_constraint(Constraint::new(
                sum,
                LinearCombination::single_term(1u64, one_index),
                output,
            ));
        }

        cs
    }

    fn cs_norm_bound(d: usize, log_bound: usize) -> ConstraintSystem<Self::Base> {
        <Self::Base as CSRing>::cs_norm_bound(d, log_bound)
    }
}

impl<R: SuitableRing> CSRing for R {
    type Base = R;

    fn cs_mul(s: Input, sp: Input, t: Input, _k: usize) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        let (s_index, sp_index, t_index, one_index) = match (s, sp, t) {
            (Input::Public, Input::Public, Input::Private) => (0, 1, 3, 2),
            (Input::Private, Input::Private, Input::Public) => (2, 3, 0, 1),
            (Input::Public, Input::Private, Input::Public)
            | (Input::Private, Input::Public, Input::Public) => (3, 0, 1, 2),
            (Input::Public, Input::Private, Input::Private)
            | (Input::Private, Input::Public, Input::Private) => (2, 0, 3, 1),
            _ => panic!("{s:?} * {sp:?} = {t:?} relation not supported"),
        };

        let nvars = 4;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        let a = LinearCombination::single_term(1u64, s_index);
        let b = LinearCombination::single_term(1u64, sp_index);
        let c = LinearCombination::single_term(1u64, t_index);
        cs.add_constraint(Constraint::new(a, b, c));

        cs
    }

    fn cs_norm_bound(d: usize, log_bound: usize) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        // Variables:
        // 0..d: input c = [c_i] (coefficients)
        // d: constant 1 (auxiliary input)
        // d+1..2d: auxiliary variables for c_i * c_i (squared coeffs)
        // 2d+1: auxiliary variable for sum of squares
        // 2d+2..2d+2+log2(bound): binary decomposition of sum
        cs.ninputs = d; // input polynomial coefficients
        cs.nauxs = d + 2 + log_bound; // d for squares + sum + binary decomposition

        // For each coefficient c_i, compute c_i * c_i
        for i in 0..d {
            let a = LinearCombination::single_term(1u64, i); // c_i
            let b = LinearCombination::single_term(1u64, i); // c_i
            let c = LinearCombination::single_term(1u64, d + 1 + i); // c_i * c_i
            cs.add_constraint(Constraint::new(a, b, c));
        }

        // Sum all squared terms
        let mut sum_terms = Vec::with_capacity(d);
        for i in 0..d {
            sum_terms.push((1u64.into(), d + 1 + i));
        }
        let sum = LinearCombination::new().add_terms(&sum_terms);
        let output = LinearCombination::single_term(1u64, 2 * d + 1);
        // sum * 1 = output
        cs.add_constraint(Constraint::new(
            sum,
            LinearCombination::single_term(1u64, d),
            output,
        ));

        // Binary decomposition of the sum
        // Each bit must be 0 or 1 (bit * bit = bit)
        for i in 0..log_bound {
            let bit = LinearCombination::single_term(1u64, 2 * d + 2 + i);
            cs.add_constraint(Constraint::new(bit.clone(), bit.clone(), bit));
        }

        // Enforce that the sum equals the binary decomposition
        let mut binary_terms: Vec<(R, usize)> = Vec::with_capacity(log_bound);
        for i in 0..log_bound {
            binary_terms.push(((1u64 << i).into(), 2 * d + 2 + i));
        }
        let binary_sum = LinearCombination::new().add_terms(&binary_terms);

        // sum = binary_sum
        cs.add_constraint(Constraint::new(
            LinearCombination::single_term(1u64, 2 * d + 1),
            LinearCombination::single_term(1u64, d),
            binary_sum,
        ));

        cs
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Input {
    /// Public input (x)
    Public,
    /// Witness (w)
    Private,
}

/// Combine several constraint systems into a single R1CS instance
pub struct R1CSBuilder<R: CSRing> {
    pub systems: Vec<ConstraintSystem<R::Base>>,
}

impl<R: CSRing> R1CSBuilder<R> {
    pub fn new() -> R1CSBuilder<R> {
        Self { systems: vec![] }
    }

    pub fn push(&mut self, cs: ConstraintSystem<R::Base>) {
        self.systems.push(cs);
    }

    pub fn build(self) -> R1CS<R::Base> {
        let nconstraints = self.systems.iter().map(|s| s.nconstraints()).sum();

        // z = (x || 1 || w)
        let input_len = self.systems.iter().map(|s| s.ninputs).sum();
        let witness_len = self.systems.iter().map(|s| s.nauxs - 1).sum::<usize>();
        let nvars = input_len + 1 + witness_len;

        let mut a = SparseMatrix {
            n_rows: nconstraints,
            n_cols: nvars,
            coeffs: vec![vec![]; nconstraints],
        };

        let mut b = SparseMatrix {
            n_rows: nconstraints,
            n_cols: nvars,
            coeffs: vec![vec![]; nconstraints],
        };

        let mut c = SparseMatrix {
            n_rows: nconstraints,
            n_cols: nvars,
            coeffs: vec![vec![]; nconstraints],
        };

        let mut constraint_offset = 0;
        let mut input_offset = 0;
        let one_offset = input_len;
        let mut witness_offset = input_len + 1;

        for system in self.systems.iter() {
            for (i, constraint) in system.constraints.iter().enumerate() {
                let row = i + constraint_offset;

                let map_var = |index: usize| -> usize {
                    match index.cmp(&system.ninputs) {
                        Ordering::Less => index + input_offset,
                        Ordering::Equal => one_offset,
                        Ordering::Greater => (index - system.ninputs - 1) + witness_offset,
                    }
                };

                for &(v, index) in &constraint.a.terms {
                    a.coeffs[row].push((v, map_var(index)));
                }
                for &(v, index) in &constraint.b.terms {
                    b.coeffs[row].push((v, map_var(index)));
                }
                for &(v, index) in &constraint.c.terms {
                    c.coeffs[row].push((v, map_var(index)));
                }
            }

            constraint_offset += system.nconstraints();
            input_offset += system.ninputs;
            witness_offset += system.nauxs - 1;
        }

        R1CS {
            l: input_len,
            A: a,
            B: b,
            C: c,
        }
    }
}

impl<R: CSRing> Default for R1CSBuilder<R> {
    fn default() -> Self {
        Self::new()
    }
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
    use cyclotomic_rings::rings::{FrogRingNTT as RqNTT, FrogRingPoly as RqPoly};
    use rand::Rng;
    use stark_rings::PolyRing;

    #[test]
    fn test_r1cs_ring_mul_ppw() {
        let r1cs = RqNTT::cs_mul(Input::Public, Input::Public, Input::Private, 0).to_r1cs();
        // 2*3 = 6
        let z = &[
            RqNTT::from(2u32),
            RqNTT::from(3u32),
            RqNTT::from(1u32),
            RqNTT::from(6u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_mul_wwp() {
        let r1cs = RqNTT::cs_mul(Input::Private, Input::Private, Input::Public, 0).to_r1cs();
        // 2*3 = 6
        let z = &[
            RqNTT::from(6u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(3u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_mul_wpw() {
        let r1cs = RqNTT::cs_mul(Input::Private, Input::Public, Input::Private, 0).to_r1cs();
        // 2*3 = 6
        let z = &[
            RqNTT::from(3u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(6u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_mul_wpp() {
        let r1cs = RqNTT::cs_mul(Input::Private, Input::Public, Input::Public, 0).to_r1cs();
        // 2*3 = 6
        let z = &[
            RqNTT::from(3u32),
            RqNTT::from(6u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

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
    fn test_r1cs_composite_signature_verification_double() {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(signature_verification_cs());
        builder.push(signature_verification_cs());
        let r1cs = builder.build();

        // 1 + 2*3 = 7
        // 1 + 2*3 = 7
        let z = &[
            RqNTT::from(7u32),
            RqNTT::from(3u32),
            RqNTT::from(7u32),
            RqNTT::from(3u32),
            RqNTT::from(1u32), // one
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(6u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(6u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    fn splitring_mul_setup(
        k: usize,
    ) -> (SplitRing<RqNTT>, SplitRing<RqNTT>, Vec<RqNTT>, Vec<RqNTT>) {
        // 5X^10 * 5X^10 = 25X^20
        let mut a_r = vec![0u128; 512];
        a_r[10] = 5;
        let mut b_r = vec![0u128; 512];
        b_r[10] = 5;

        let a: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&a_r).crt();
        let b: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&b_r).crt();
        let c: SplitRing<RqNTT> = a.clone() * b.clone();

        // cross-multiplication terms s_i*s'_j
        let mut aux = vec![RqNTT::from(0u32); k * k];
        for i in 0..k {
            for j in 0..k {
                let aux_idx = i * k + j;
                aux[aux_idx] = a[i] * b[j];
            }
        }

        // output poly t = [t_l]
        let mut t = vec![RqNTT::from(0u32); k];
        for (l, tl) in t.iter_mut().enumerate() {
            for i in 0..k {
                for j in 0..k {
                    if (i + j) % k == l {
                        *tl += aux[i * k + j];
                    }
                }
            }
        }
        assert_eq!(t, c.splits()); // assert summation

        (a, b, t, aux)
    }

    #[test]
    fn test_r1cs_splitring_mul_ppw() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_mul(Input::Public, Input::Public, Input::Private, k).to_r1cs();
        let (a, b, t, aux) = splitring_mul_setup(k);
        let mut z = Vec::with_capacity(3 * k + k * k + 1); // inputs + constant 1 + aux + output

        // public inputs s, s'
        z.extend(a.splits());
        z.extend(b.splits());

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness (mul result)
        z.extend(t);

        z.extend(aux);

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_mul_wwp() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_mul(Input::Private, Input::Private, Input::Public, k).to_r1cs();
        let (a, b, t, aux) = splitring_mul_setup(k);
        let mut z = Vec::with_capacity(3 * k + k * k + 1); // inputs + constant 1 + aux + output

        // public input (mul result)
        z.extend(t);

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness s, s'
        z.extend(a.splits());
        z.extend(b.splits());

        z.extend(aux);

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_mul_wpp() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_mul(Input::Private, Input::Public, Input::Public, k).to_r1cs();
        let (a, b, t, aux) = splitring_mul_setup(k);
        let mut z = Vec::with_capacity(3 * k + k * k + 1); // inputs + constant 1 + aux + output

        // public inputs (s', mul result)
        z.extend(b.splits());
        z.extend(t);

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness s
        z.extend(a.splits());

        z.extend(aux);

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_mul_wpw() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_mul(Input::Private, Input::Public, Input::Private, k).to_r1cs();
        let (a, b, t, aux) = splitring_mul_setup(k);
        let mut z = Vec::with_capacity(3 * k + k * k + 1); // inputs + constant 1 + aux + output

        // public inputs s'
        z.extend(b.splits());

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness s, mul result
        z.extend(a.splits());
        z.extend(t);

        z.extend(aux);

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_norm_bound() {
        let mut rng = rand::thread_rng();
        let bound = 16; // 2^16
        let d = 512;
        let r1cs = RqNTT::cs_norm_bound(d, bound).to_r1cs();

        let a_r = (0..d).map(|_| rng.gen_range(0..10)).collect::<Vec<_>>();
        let norm: u128 = a_r.iter().map(|x| x * x).sum();
        assert!(norm < (1u128 << bound));

        let mut z = Vec::with_capacity(d + 2 + bound);

        z.extend(
            a_r.iter()
                .map(|&x| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(x))),
        ); // coeffs

        z.push(RqNTT::from(1u32)); // constant 1

        a_r.iter().for_each(|coeff| {
            z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
                coeff * coeff,
            )))
        }); // squared coeffs

        z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
            norm,
        ))); // squared norm

        // Norm binary decomposition
        let mut remaining = norm;
        for i in 0..bound {
            let bit = if (remaining & (1 << i)) != 0 {
                remaining -= 1 << i;
                RqNTT::from(1u32)
            } else {
                RqNTT::from(0u32)
            };
            z.push(bit);
        }

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_norm_bound() {
        let mut rng = rand::thread_rng();
        let bound = 16; // 2^16
        let d = 512;
        let r1cs = SplitRing::<RqNTT>::cs_norm_bound(d, bound).to_r1cs();

        let a_r = (0..d).map(|_| rng.gen_range(0..10)).collect::<Vec<_>>();

        let norm: u128 = a_r.iter().map(|x| x * x).sum();
        assert!(norm < (1u128 << bound));

        let mut z = Vec::with_capacity(d + 2 + bound);

        // public input poly
        z.extend(
            a_r.iter()
                .map(|&x| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(x))),
        );

        // one
        z.push(RqNTT::from(1u32));

        // aux: c_i * c_i
        a_r.iter().for_each(|coeff| {
            z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
                coeff * coeff,
            )))
        });

        // squared norm
        z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
            norm,
        )));

        let mut remaining = norm;
        for i in 0..bound {
            let bit = if (remaining & (1 << i)) != 0 {
                remaining -= 1 << i;
                RqNTT::from(1u32)
            } else {
                RqNTT::from(0u32)
            };
            z.push(bit);
        }

        r1cs.check_relation(&z).unwrap();
    }
}
