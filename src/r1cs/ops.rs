use crate::SplitRing;
use cyclotomic_rings::rings::SuitableRing;
use latticefold::arith::r1cs::{Constraint, ConstraintSystem, LinearCombination};

pub trait CSRing {
    type Base: SuitableRing;

    /// Addition constraint system for rings, `s + sp = t`.
    /// `k` is the number of splits for a [`SplitRing`]
    fn cs_add(s: Input, sp: Input, t: Input, k: usize) -> ConstraintSystem<Self::Base>;

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

    fn cs_add(s: Input, sp: Input, t: Input, k: usize) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        // Variables (one witness ring):
        // 0..k: public ring
        // k..2k: public ring
        // 2k: constant 1
        // 2k+1..3k+1: private ring

        // Variables (two witness rings):
        // 0..k: public ring
        // k: constant 1
        // k+1..2k+1: private ring
        // 2k+1..3k+1: private ring

        let (s_index, sp_index, t_index, one_index) = match (s, sp, t) {
            (Input::Public, Input::Public, Input::Private) => (0, k, 2 * k + 1, 2 * k),
            (Input::Private, Input::Private, Input::Public) => (k + 1, 2 * k + 1, 0, k),
            (Input::Public, Input::Private, Input::Public)
            | (Input::Private, Input::Public, Input::Public) => (0, 2 * k + 1, k, 2 * k),
            (Input::Public, Input::Private, Input::Private)
            | (Input::Private, Input::Public, Input::Private) => (0, k + 1, 2 * k + 1, k),
            _ => panic!("{s:?} + {sp:?} = {t:?} relation not supported"),
        };

        let nvars = 3 * k + 1;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // For each split, s_l + s'_l = t_l
        for l in 0..k {
            let a = LinearCombination::new()
                .add_term(1u64, s_index + l)
                .add_term(1u64, sp_index + l);
            let b = LinearCombination::single_term(1u64, one_index);
            let c = LinearCombination::single_term(1u64, t_index + l);
            cs.add_constraint(Constraint::new(a, b, c));
        }

        cs
    }

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

    fn cs_add(s: Input, sp: Input, t: Input, _k: usize) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        let (s_index, sp_index, t_index, one_index) = match (s, sp, t) {
            (Input::Public, Input::Public, Input::Private) => (0, 1, 3, 2),
            (Input::Private, Input::Private, Input::Public) => (2, 3, 0, 1),
            (Input::Public, Input::Private, Input::Public)
            | (Input::Private, Input::Public, Input::Public) => (3, 0, 1, 2),
            (Input::Public, Input::Private, Input::Private)
            | (Input::Private, Input::Public, Input::Private) => (2, 0, 3, 1),
            _ => panic!("{s:?} + {sp:?} = {t:?} relation not supported"),
        };

        let nvars = 4;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        let a = LinearCombination::new()
            .add_term(1u64, s_index)
            .add_term(1u64, sp_index);
        let b = LinearCombination::single_term(1u64, one_index);
        let c = LinearCombination::single_term(1u64, t_index);
        cs.add_constraint(Constraint::new(a, b, c));

        cs
    }

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

    #[test]
    fn test_r1cs_ring_add_ppw() {
        let r1cs = RqNTT::cs_add(Input::Public, Input::Public, Input::Private, 0).to_r1cs();
        // 2+3 = 5
        let z = &[
            RqNTT::from(2u32),
            RqNTT::from(3u32),
            RqNTT::from(1u32),
            RqNTT::from(5u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_add_wwp() {
        let r1cs = RqNTT::cs_add(Input::Private, Input::Private, Input::Public, 0).to_r1cs();
        // 2+3 = 5
        let z = &[
            RqNTT::from(5u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(3u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_add_wpw() {
        let r1cs = RqNTT::cs_add(Input::Private, Input::Public, Input::Private, 0).to_r1cs();
        // 2+3 = 5
        let z = &[
            RqNTT::from(3u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
            RqNTT::from(5u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_add_wpp() {
        let r1cs = RqNTT::cs_add(Input::Private, Input::Public, Input::Public, 0).to_r1cs();
        // 2+3 = 5
        let z = &[
            RqNTT::from(3u32),
            RqNTT::from(5u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    fn splitring_add_setup(k: usize) -> (SplitRing<RqNTT>, SplitRing<RqNTT>, Vec<RqNTT>) {
        // 5X^10 + 3X^10 = 8X^10
        let mut a_r = vec![0u128; 512];
        a_r[10] = 5;
        let mut b_r = vec![0u128; 512];
        b_r[10] = 3;

        let a: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&a_r).crt();
        let b: SplitRing<RqNTT> = SplitRingPoly::<RqPoly>::from_r(&b_r).crt();
        let c: SplitRing<RqNTT> = a.clone() + b.clone();

        // output poly t = [t_l]
        let t = c.splits().to_vec();
        assert_eq!(t.len(), k);

        (a, b, t)
    }

    #[test]
    fn test_r1cs_splitring_add_ppw() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_add(Input::Public, Input::Public, Input::Private, k).to_r1cs();
        let (a, b, t) = splitring_add_setup(k);
        let mut z = Vec::with_capacity(3 * k + 1); // inputs + constant 1 + output

        // public inputs s, s'
        z.extend(a.splits());
        z.extend(b.splits());

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness (add result)
        z.extend(t);

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_add_wwp() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_add(Input::Private, Input::Private, Input::Public, k).to_r1cs();
        let (a, b, t) = splitring_add_setup(k);
        let mut z = Vec::with_capacity(3 * k + 1); // inputs + constant 1 + output

        // public input (add result)
        z.extend(t);

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness s, s'
        z.extend(a.splits());
        z.extend(b.splits());

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_add_wpp() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_add(Input::Private, Input::Public, Input::Public, k).to_r1cs();
        let (a, b, t) = splitring_add_setup(k);
        let mut z = Vec::with_capacity(3 * k + 1); // inputs + constant 1 + output

        // public inputs (s', add result)
        z.extend(b.splits());
        z.extend(t);

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness s
        z.extend(a.splits());

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_add_wpw() {
        // Falcon degree = 512, Frog ring of degree 16
        let k = 32; // n subrings
        let r1cs = SplitRing::cs_add(Input::Private, Input::Public, Input::Private, k).to_r1cs();
        let (a, b, t) = splitring_add_setup(k);
        let mut z = Vec::with_capacity(3 * k + 1); // inputs + constant 1 + output

        // public inputs s'
        z.extend(b.splits());

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness s, add result
        z.extend(a.splits());
        z.extend(t);

        r1cs.check_relation(&z).unwrap();
    }
}
