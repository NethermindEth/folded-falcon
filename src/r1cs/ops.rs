use crate::SplitRing;
use cyclotomic_rings::rings::SuitableRing;
use latticefold::arith::r1cs::{Constraint, ConstraintSystem, LinearCombination};
use stark_rings::{
    PolyRing, Ring,
    cyclotomic_ring::{
        CRT, CyclotomicConfig, CyclotomicPolyRingGeneral, CyclotomicPolyRingNTTGeneral, ICRT,
    },
};
use std::ops::Neg;

pub trait CSRing {
    type Base: SuitableRing;

    /// Addition constraint system for rings, `s + sp = t`.
    fn cs_add(s: Input, sp: Input, t: Input) -> ConstraintSystem<Self::Base>;

    /// Multiplication constraint system for rings, `s * sp = t`.
    fn cs_mul(s: Input, sp: Input, t: Input) -> ConstraintSystem<Self::Base>;

    /// Lifting term constraint system for rings, `s - sp = t`.
    /// `sp` is multiplied by a modulus `p` to get a lifting factor.
    fn cs_liftsub(s: Input, sp: Input, t: Input, p: u128) -> ConstraintSystem<Self::Base>;

    /// CS with l2- norm calculation, norm bound constraints, for some poly of degree `d`.
    /// `log_bound` must be the log2 of the norm bound. Only powers of 2 bounds are currently supported.
    /// The norm is constrained to be representable with only `log_bound` bits.
    fn cs_norm_bound(x: Input, d: usize, log_bound: usize) -> ConstraintSystem<Self::Base>;

    /// CS with l2- norm calculation, norm bound constraints, for two polynomials of degree `d`.
    /// `log_bound` must be the log2 of the norm bound. Only powers of 2 bounds are currently supported.
    /// The norm is constrained to be representable with only `log_bound` bits.
    fn cs_norm_bound_xy(
        x: Input,
        y: Input,
        d: usize,
        log_bound: usize,
    ) -> ConstraintSystem<Self::Base>;

    /// CS stating that `x` is composed by `d` `coeffs`.
    fn cs_combine(x: Input, coeffs: Input, d: usize) -> ConstraintSystem<Self::Base>;
}

impl<R: SuitableRing + UnitMonomial, const K: usize> CSRing for SplitRing<R, K> {
    type Base = R;

    fn cs_add(s: Input, sp: Input, t: Input) -> ConstraintSystem<R> {
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

        let (s_index, sp_index, t_index, one_index) = match (s.ty, sp.ty, t.ty) {
            (InputType::Public, InputType::Public, InputType::Private) => (0, K, 2 * K + 1, 2 * K),
            (InputType::Private, InputType::Private, InputType::Public) => (K + 1, 2 * K + 1, 0, K),
            (InputType::Public, InputType::Private, InputType::Public) => (0, 2 * K + 1, K, 2 * K),
            (InputType::Private, InputType::Public, InputType::Public) => (2 * K + 1, 0, K, 2 * K),
            (InputType::Public, InputType::Private, InputType::Private) => (0, K + 1, 2 * K + 1, K),
            (InputType::Private, InputType::Public, InputType::Private) => (K + 1, 0, 2 * K + 1, K),
            // All private inputs: should only be used with other systems
            (InputType::Private, InputType::Private, InputType::Private) => {
                (1, K + 1, 2 * K + 1, 0)
            }
            _ => panic!("{s:?} + {sp:?} = {t:?} relation not supported"),
        };

        cs.vars.add(s.name, s_index, K);
        cs.vars.add(sp.name, sp_index, K);
        cs.vars.add(t.name, t_index, K);
        cs.vars.set_one(one_index);

        let nvars = 3 * K + 1;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // For each split, s_l + s'_l = t_l
        for l in 0..K {
            let a = LinearCombination::new()
                .add_term(1u64, s_index + l)
                .add_term(1u64, sp_index + l);
            let b = LinearCombination::single_term(1u64, one_index);
            let c = LinearCombination::single_term(1u64, t_index + l);
            cs.add_constraint(Constraint::new(a, b, c));
        }

        cs
    }

    fn cs_liftsub(s: Input, sp: Input, t: Input, p: u128) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        // Variables (one witness ring):
        // 0..k: public ring
        // k..2k: public ring
        // 2k: constant 1
        // 2k+1..3k+1: private ring
        let (s_index, sp_index, t_index, one_index) = match (s.ty, sp.ty, t.ty) {
            (InputType::Public, InputType::Public, InputType::Private) => (0, K, 2 * K + 1, 2 * K),
            (InputType::Private, InputType::Private, InputType::Public) => (K + 1, 2 * K + 1, 0, K),
            (InputType::Public, InputType::Private, InputType::Public) => (0, 2 * K + 1, K, 2 * K),
            (InputType::Private, InputType::Public, InputType::Public) => (2 * K + 1, 0, K, 2 * K),
            (InputType::Public, InputType::Private, InputType::Private) => (0, K + 1, 2 * K + 1, K),
            (InputType::Private, InputType::Public, InputType::Private) => (K + 1, 0, 2 * K + 1, K),
            // All private inputs: should only be used with other systems
            (InputType::Private, InputType::Private, InputType::Private) => {
                (1, K + 1, 2 * K + 1, 0)
            }
            _ => panic!("{s:?} - {sp:?} = {t:?} relation not supported"),
        };

        cs.vars.add(s.name, s_index, K);
        cs.vars.add(sp.name, sp_index, K);
        cs.vars.add(t.name, t_index, K);
        cs.vars.set_one(one_index);

        let nvars = 3 * K + 1;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // For each split, s_l - p*s'_l = t_l
        for l in 0..K {
            let a = LinearCombination::new()
                .add_term(1u64, s_index + l)
                .add_term(
                    <Self::Base as PolyRing>::from_scalar(
                        <Self::Base as PolyRing>::BaseRing::from(p).neg(),
                    ),
                    sp_index + l,
                );
            let b = LinearCombination::single_term(1u64, one_index);
            let c = LinearCombination::single_term(1u64, t_index + l);
            cs.add_constraint(Constraint::new(a, b, c));
        }

        cs
    }

    fn cs_mul(s: Input, sp: Input, t: Input) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        let (s_index, sp_index, t_index, one_index) = match (s.ty, sp.ty, t.ty) {
            (InputType::Public, InputType::Public, InputType::Private) => (0, K, 2 * K + 1, 2 * K),
            (InputType::Private, InputType::Private, InputType::Public) => (K + 1, 2 * K + 1, 0, K),
            (InputType::Public, InputType::Private, InputType::Public) => (0, 2 * K + 1, K, 2 * K),
            (InputType::Private, InputType::Public, InputType::Public) => (2 * K + 1, 0, K, 2 * K),
            (InputType::Public, InputType::Private, InputType::Private) => (0, K + 1, 2 * K + 1, K),
            (InputType::Private, InputType::Public, InputType::Private) => (K + 1, 0, 2 * K + 1, K),
            // All private inputs: should only be used with other systems
            (InputType::Private, InputType::Private, InputType::Private) => {
                (1, K + 1, 2 * K + 1, 0)
            }
            _ => panic!("{s:?} * {sp:?} = {t:?} relation not supported"),
        };

        cs.vars.add(s.name.clone(), s_index, K);
        cs.vars.add(sp.name.clone(), sp_index, K);
        cs.vars.add(t.name, t_index, K);
        cs.vars.set_one(one_index);
        cs.vars
            .add(format!("{}*{}", s.name, sp.name), 3 * K + 1, K * K);

        let nvars = K + K + K + 1 + K * K;
        let aux_index = 3 * K + 1;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // For each t_l
        for l in 0..K {
            // Multiplication constraints for each s_i*s'_j
            for i in 0..K {
                for j in 0..K {
                    if (i + j) % K == l {
                        let w = (i + j) / K;
                        let mut x = R::CoefficientRepresentation::ZERO;
                        x.coeffs_mut()[w] = 1u32.into();
                        let aux_idx = aux_index + i * K + j;
                        let a = LinearCombination::single_term(x.crt(), s_index + i);
                        let b = LinearCombination::single_term(1u64, sp_index + j);
                        let c = LinearCombination::single_term(1u64, aux_idx);
                        cs.add_constraint(Constraint::new(a, b, c));
                    }
                }
            }

            // Addition constraint for the sum of s_i*s'_j which composes t_l
            let mut sum_terms = Vec::new();
            for i in 0..K {
                for j in 0..K {
                    if (i + j) % K == l {
                        let aux_idx = aux_index + i * K + j;
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

    fn cs_norm_bound(x: Input, d: usize, log_bound: usize) -> ConstraintSystem<Self::Base> {
        <Self::Base as CSRing>::cs_norm_bound(x, d, log_bound)
    }

    fn cs_norm_bound_xy(
        x: Input,
        y: Input,
        d: usize,
        log_bound: usize,
    ) -> ConstraintSystem<Self::Base> {
        <Self::Base as CSRing>::cs_norm_bound_xy(x, y, d, log_bound)
    }

    fn cs_combine(x: Input, coeffs: Input, d: usize) -> ConstraintSystem<Self::Base> {
        let mut cs = ConstraintSystem::<R>::new();
        let b = d / K;

        let (x_index, coeffs_index, one_index) = match (x.ty, coeffs.ty) {
            (InputType::Public, InputType::Public) => (0, K, d + 1),
            (InputType::Public, InputType::Private) => (0, K + 1, K),
            (InputType::Private, InputType::Public) => (d + 1, 0, d),
            (InputType::Private, InputType::Private) => (1, K + 1, 0),
        };

        cs.vars.add(x.name.clone(), x_index, K);
        cs.vars.add(coeffs.name.clone(), coeffs_index, K * d);
        cs.vars.set_one(one_index);

        let nvars = K + d + 1;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // coeffs in order of x_0, x_1, ..., x_{k-1}
        // splitring0 = [x_0, x_k, x_{2k}, ..., x_{(d-1)k}]
        // splitring1 = [x_1, x_{k+1}, x_{2k+1}, ..., x_{(d-1)k+1}]
        // ...

        // for each splitring, add a constraint
        for i in 0..K {
            let mut sum_terms = Vec::new();
            for j in 0..b {
                sum_terms.push((R::unit_monomial(j), coeffs_index + j * K + i));
            }
            let sum = LinearCombination::new().add_terms(&sum_terms);
            let output = LinearCombination::single_term(1u64, x_index + i);
            cs.add_constraint(Constraint::new(
                sum,
                LinearCombination::single_term(1u64, one_index),
                output,
            ));
        }

        cs
    }
}

impl<R: SuitableRing + UnitMonomial> CSRing for R {
    type Base = R;

    fn cs_add(s: Input, sp: Input, t: Input) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        let (s_index, sp_index, t_index, one_index) = match (s.ty, sp.ty, t.ty) {
            (InputType::Public, InputType::Public, InputType::Private) => (0, 1, 3, 2),
            (InputType::Private, InputType::Private, InputType::Public) => (2, 3, 0, 1),
            (InputType::Public, InputType::Private, InputType::Public) => (0, 3, 1, 2),
            (InputType::Private, InputType::Public, InputType::Public) => (3, 0, 1, 2),
            (InputType::Public, InputType::Private, InputType::Private) => (0, 2, 3, 1),
            (InputType::Private, InputType::Public, InputType::Private) => (2, 0, 3, 1),
            // All private inputs: should only be used with other systems
            (InputType::Private, InputType::Private, InputType::Private) => (1, 2, 3, 0),
            _ => panic!("{s:?} + {sp:?} = {t:?} relation not supported"),
        };

        cs.vars.add(s.name, s_index, 1);
        cs.vars.add(sp.name, sp_index, 1);
        cs.vars.add(t.name, t_index, 1);
        cs.vars.set_one(one_index);

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

    fn cs_mul(s: Input, sp: Input, t: Input) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        let (s_index, sp_index, t_index, one_index) = match (s.ty, sp.ty, t.ty) {
            (InputType::Public, InputType::Public, InputType::Private) => (0, 1, 3, 2),
            (InputType::Private, InputType::Private, InputType::Public) => (2, 3, 0, 1),
            (InputType::Public, InputType::Private, InputType::Public) => (0, 3, 1, 2),
            (InputType::Private, InputType::Public, InputType::Public) => (3, 0, 1, 2),
            (InputType::Public, InputType::Private, InputType::Private) => (0, 2, 3, 1),
            (InputType::Private, InputType::Public, InputType::Private) => (2, 0, 3, 1),
            // All private inputs: should only be used with other systems
            (InputType::Private, InputType::Private, InputType::Private) => (1, 2, 3, 0),
            _ => panic!("{s:?} * {sp:?} = {t:?} relation not supported"),
        };

        cs.vars.add(s.name, s_index, 1);
        cs.vars.add(sp.name, sp_index, 1);
        cs.vars.add(t.name, t_index, 1);
        cs.vars.set_one(one_index);

        let nvars = 4;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        let a = LinearCombination::single_term(1u64, s_index);
        let b = LinearCombination::single_term(1u64, sp_index);
        let c = LinearCombination::single_term(1u64, t_index);
        cs.add_constraint(Constraint::new(a, b, c));

        cs
    }

    fn cs_norm_bound(x: Input, d: usize, log_bound: usize) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        // Variables:
        // 0..d: input c = [c_i] (coefficients)
        // d: constant 1 (auxiliary input)
        // d+1..2d: auxiliary variables for c_i * c_i (squared coeffs)
        // 2d+1: auxiliary variable for sum of squares
        // 2d+2..2d+2+log2(bound): binary decomposition of sum

        let (x_index, aux_index, one_index) = match x.ty {
            InputType::Public => (0, d + 1, d),
            InputType::Private => (1, d + 1, 0),
        };

        cs.vars.add(x.name.clone(), x_index, 1);
        cs.vars.set_one(one_index);
        cs.vars.add(format!("{}*{}", x.name, x.name), aux_index, d);
        cs.vars.add(format!("||{}||^2", x.name), aux_index + d, 1);
        cs.vars
            .add(format!("{} decomp", x.name), aux_index + d + 1, log_bound);

        let nvars = d + 1 + d + 1 + log_bound;
        cs.ninputs = one_index; // input polynomial coefficients
        cs.nauxs = nvars - one_index; // d for squares + sum + binary decomposition

        // For each coefficient c_i, compute c_i * c_i
        for i in 0..d {
            let a = LinearCombination::single_term(1u64, x_index + i); // c_i
            let b = LinearCombination::single_term(1u64, x_index + i); // c_i
            let c = LinearCombination::single_term(1u64, aux_index + i); // c_i * c_i
            cs.add_constraint(Constraint::new(a, b, c));
        }

        // Sum all squared terms
        let mut sum_terms = Vec::with_capacity(d);
        for i in 0..d {
            sum_terms.push((1u64.into(), aux_index + i));
        }
        let sum = LinearCombination::new().add_terms(&sum_terms);
        let output = LinearCombination::single_term(1u64, aux_index + d);
        // sum * 1 = output
        cs.add_constraint(Constraint::new(
            sum,
            LinearCombination::single_term(1u64, one_index),
            output,
        ));

        // Binary decomposition of the sum
        // Each bit must be 0 or 1 (bit * bit = bit)
        for i in 0..log_bound {
            let bit = LinearCombination::single_term(1u64, aux_index + d + 1 + i);
            cs.add_constraint(Constraint::new(bit.clone(), bit.clone(), bit));
        }

        // Enforce that the sum equals the binary decomposition
        let mut binary_terms: Vec<(R, usize)> = Vec::with_capacity(log_bound);
        for i in 0..log_bound {
            binary_terms.push(((1u64 << i).into(), aux_index + d + 1 + i));
        }
        let binary_sum = LinearCombination::new().add_terms(&binary_terms);

        // sum = binary_sum
        cs.add_constraint(Constraint::new(
            LinearCombination::single_term(1u64, aux_index + d),
            LinearCombination::single_term(1u64, one_index),
            binary_sum,
        ));

        cs
    }

    fn cs_liftsub(s: Input, sp: Input, t: Input, p: u128) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        let (s_index, sp_index, t_index, one_index) = match (s.ty, sp.ty, t.ty) {
            (InputType::Public, InputType::Public, InputType::Private) => (0, 1, 3, 2),
            (InputType::Private, InputType::Private, InputType::Public) => (2, 3, 0, 1),
            (InputType::Public, InputType::Private, InputType::Public) => (0, 3, 1, 2),
            (InputType::Private, InputType::Public, InputType::Public) => (3, 0, 1, 2),
            (InputType::Public, InputType::Private, InputType::Private) => (0, 2, 3, 1),
            (InputType::Private, InputType::Public, InputType::Private) => (2, 0, 3, 1),
            _ => panic!("{s:?} * {sp:?} = {t:?} relation not supported"),
        };

        cs.vars.add(s.name, s_index, 1);
        cs.vars.add(sp.name, sp_index, 1);
        cs.vars.add(t.name, t_index, 1);
        cs.vars.set_one(one_index);

        let nvars = 4;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        let a = LinearCombination::new().add_term(1u64, s_index).add_term(
            <Self::Base as PolyRing>::from_scalar(
                <Self::Base as PolyRing>::BaseRing::from(p).neg(),
            ),
            sp_index,
        );
        let b = LinearCombination::single_term(1u64, one_index);
        let c = LinearCombination::single_term(1u64, t_index);
        cs.add_constraint(Constraint::new(a, b, c));

        cs
    }

    fn cs_norm_bound_xy(x: Input, y: Input, d: usize, log_bound: usize) -> ConstraintSystem<R> {
        let mut cs = ConstraintSystem::<R>::new();

        // ||x||^2 + ||y||^2  < 2^log_bound

        // Variables:
        // 0..d: input x = [x_i] coefficients
        // d..2d: input y = [y_i] coefficients
        // 2d: constant 1 (auxiliary input)
        // 2d+1..3d+1: auxiliary variables for x_i * x_i (squared coeffs)
        // 3d+1..4d+1: auxiliary variables for y_i * y_i (squared coeffs)
        // 4d+1: auxiliary variable for ||x||^2
        // 4d+2: auxiliary variable for ||y||^2
        // 4d+3..4d+3+log2(bound): binary decomposition of sum

        let (x_index, y_index, aux_index, one_index) = match (x.ty, y.ty) {
            (InputType::Public, InputType::Public) => (0, d, 2 * d + 1, 2 * d),
            (InputType::Private, InputType::Private) => (1, d + 1, 2 * d + 1, 0),
            (InputType::Public, InputType::Private) => (0, d + 1, 2 * d + 1, d),
            (InputType::Private, InputType::Public) => (d + 1, 0, 2 * d + 1, d),
        };

        cs.vars.add(x.name.clone(), x_index, d);
        cs.vars.add(y.name.clone(), y_index, d);
        cs.vars.set_one(one_index);
        cs.vars.add(format!("{}*{}", x.name, x.name), aux_index, d);
        cs.vars
            .add(format!("{}*{}", y.name, y.name), aux_index + d, d);
        cs.vars
            .add(format!("||{}||^2", x.name), aux_index + 2 * d, 1);
        cs.vars
            .add(format!("||{}||^2", y.name), aux_index + 2 * d + 1, 1);
        cs.vars.add(
            format!("||{},{}||^2 decomp", x.name, y.name),
            aux_index + 2 * d + 2,
            log_bound,
        );

        let nvars = d + d + 1 + d + d + 1 + 1 + log_bound;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // For each coefficient x_i, compute x_i * x_i
        for i in 0..d {
            let a = LinearCombination::single_term(1u64, x_index + i); // x_i
            let b = LinearCombination::single_term(1u64, x_index + i); // x_i
            let c = LinearCombination::single_term(1u64, aux_index + i); // x_i * x_i
            cs.add_constraint(Constraint::new(a, b, c));
        }

        // For each coefficient y_i, compute y_i * y_i
        for i in 0..d {
            let a = LinearCombination::single_term(1u64, y_index + i); // y_i
            let b = LinearCombination::single_term(1u64, y_index + i); // y_i
            let c = LinearCombination::single_term(1u64, aux_index + d + i); // y_i * y_i
            cs.add_constraint(Constraint::new(a, b, c));
        }

        // sum of squares for x
        let mut sum_terms_x = Vec::with_capacity(d);
        for i in 0..d {
            sum_terms_x.push((1u64.into(), aux_index + i));
        }
        let sum_x = LinearCombination::new().add_terms(&sum_terms_x);
        let output_x = LinearCombination::single_term(1u64, aux_index + 2 * d);
        cs.add_constraint(Constraint::new(
            sum_x,
            LinearCombination::single_term(1u64, one_index),
            output_x,
        ));

        // sum of squares for y
        let mut sum_terms_y = Vec::with_capacity(d);
        for i in 0..d {
            sum_terms_y.push((1u64.into(), aux_index + d + i));
        }
        let sum_y = LinearCombination::new().add_terms(&sum_terms_y);
        let output_y = LinearCombination::single_term(1u64, aux_index + 2 * d + 1);
        cs.add_constraint(Constraint::new(
            sum_y,
            LinearCombination::single_term(1u64, one_index),
            output_y,
        ));

        // binary decomposition of the sum
        for i in 0..log_bound {
            let bit = LinearCombination::single_term(1u64, aux_index + 2 * d + 2 + i);
            cs.add_constraint(Constraint::new(bit.clone(), bit.clone(), bit));
        }

        // total sum = binary_sum
        let mut binary_terms: Vec<(R, usize)> = Vec::with_capacity(log_bound);
        for i in 0..log_bound {
            binary_terms.push(((1u64 << i).into(), aux_index + 2 * d + 2 + i));
        }
        let binary_sum = LinearCombination::new().add_terms(&binary_terms);

        // ||x||^2 + ||y||^2 = binary_sum
        let total_sum = LinearCombination::new()
            .add_term(1u64, aux_index + 2 * d) // ||x||^2
            .add_term(1u64, aux_index + 2 * d + 1); // ||y||^2
        cs.add_constraint(Constraint::new(
            total_sum,
            LinearCombination::single_term(1u64, one_index),
            binary_sum,
        ));

        cs
    }

    fn cs_combine(x: Input, coeffs: Input, d: usize) -> ConstraintSystem<Self::Base> {
        let mut cs = ConstraintSystem::<R>::new();

        let (x_index, coeffs_index, one_index) = match (x.ty, coeffs.ty) {
            (InputType::Public, InputType::Public) => (0, 1, d + 1),
            (InputType::Public, InputType::Private) => (0, 2, 1),
            (InputType::Private, InputType::Public) => (d + 1, 0, d),
            (InputType::Private, InputType::Private) => (1, 2, 0),
        };

        cs.vars.add(x.name.clone(), x_index, 1);
        cs.vars.add(coeffs.name.clone(), coeffs_index, d);
        cs.vars.set_one(one_index);

        let nvars = d + 1 + 1;
        cs.ninputs = one_index;
        cs.nauxs = nvars - one_index;

        // sum of id * coeffs[i] = x
        // where id is a polynomial with a single coefficient 1 at position i
        let mut sum_terms = Vec::new();
        for i in 0..d {
            sum_terms.push((R::unit_monomial(i), coeffs_index + i));
        }

        let sum = LinearCombination::new().add_terms(&sum_terms);
        let output = LinearCombination::single_term(1u64, x_index);

        // sum * 1 = output
        cs.add_constraint(Constraint::new(
            sum,
            LinearCombination::single_term(1u64, one_index),
            output,
        ));

        cs
    }
}

pub trait UnitMonomial {
    fn unit_monomial(d: usize) -> Self;
}

impl<C: CyclotomicConfig<N>, const N: usize, const D: usize> UnitMonomial
    for CyclotomicPolyRingNTTGeneral<C, N, D>
where
    Self: ICRT<ICRTForm: PolyRing + CRT<CRTForm = Self>>,
{
    fn unit_monomial(d: usize) -> Self {
        let mut mono = Self::ZERO.icrt();
        mono.coeffs_mut()[d] = <<Self as ICRT>::ICRTForm as PolyRing>::BaseRing::ONE;
        mono.crt()
    }
}

impl<C: CyclotomicConfig<N>, const N: usize, const D: usize> UnitMonomial
    for CyclotomicPolyRingGeneral<C, N, D>
{
    fn unit_monomial(d: usize) -> Self {
        let mut mono = Self::ZERO;
        mono.coeffs_mut()[d] = <Self as PolyRing>::BaseRing::ONE;
        mono
    }
}

#[derive(Clone, Debug)]
pub struct Input {
    name: String,
    ty: InputType,
}

impl Input {
    pub fn public(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ty: InputType::Public,
        }
    }

    pub fn private(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            ty: InputType::Private,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum InputType {
    /// Public input (x)
    Public,
    /// Witness (w)
    Private,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{FALCON_MOD, SplitRing, SplitRingPoly};
    use cyclotomic_rings::rings::{FrogRingNTT as RqNTT, FrogRingPoly as RqPoly};
    use rand::Rng;

    const K: usize = 32;
    type SplitNTT = SplitRing<RqNTT, K>;
    type SplitPoly = SplitRingPoly<RqPoly, K>;

    #[test]
    fn test_r1cs_ring_mul_ppw() {
        let r1cs =
            RqNTT::cs_mul(Input::public("a"), Input::public("b"), Input::private("c")).to_r1cs();
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
        let r1cs =
            RqNTT::cs_mul(Input::private("a"), Input::private("b"), Input::public("c")).to_r1cs();
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
        let r1cs =
            RqNTT::cs_mul(Input::private("a"), Input::public("b"), Input::private("c")).to_r1cs();
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
        let r1cs =
            RqNTT::cs_mul(Input::private("a"), Input::public("b"), Input::public("c")).to_r1cs();
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
    fn test_r1cs_ring_lift_term() {
        let r1cs = RqNTT::cs_liftsub(
            Input::public("a"),
            Input::private("b"),
            Input::private("c"),
            FALCON_MOD.into(),
        )
        .to_r1cs();
        // 15000 - pv = 2711
        let z = &[
            RqNTT::from(15000u32),
            RqNTT::from(1u32),
            RqNTT::from(1u32),
            RqNTT::from(2711u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    fn splitring_mul_setup(
        a_r: &[u128],
        b_r: &[u128],
    ) -> (SplitNTT, SplitNTT, Vec<RqNTT>, Vec<RqNTT>) {
        let a = SplitPoly::from_r(a_r).crt();
        let b = SplitPoly::from_r(b_r).crt();
        let c = a.clone() * b.clone();

        // cross-multiplication terms s_i*s'_j
        let mut aux = vec![RqNTT::from(0u32); K * K];
        for i in 0..K {
            for j in 0..K {
                let aux_idx = i * K + j;
                aux[aux_idx] = a[i] * b[j];
            }
        }

        // output poly t = [t_l]
        let mut t = vec![RqNTT::from(0u32); K];
        for (l, tl) in t.iter_mut().enumerate() {
            for i in 0..K {
                for j in 0..K {
                    if (i + j) % K == l {
                        *tl += aux[i * K + j];
                    }
                }
            }
        }
        assert_eq!(t, c.splits()); // assert summation

        (a, b, t, aux)
    }

    fn splitring_mul_setup_0() -> (SplitNTT, SplitNTT, Vec<RqNTT>, Vec<RqNTT>) {
        // 5X^10 * 5X^10 = 25X^20
        let mut a_r = vec![0u128; 512];
        a_r[10] = 5;
        let mut b_r = vec![0u128; 512];
        b_r[10] = 5;

        splitring_mul_setup(&a_r, &b_r)
    }

    fn splitring_mul_setup_1() -> (SplitNTT, SplitNTT, Vec<RqNTT>, Vec<RqNTT>) {
        // X^300 * X^300 = -1X^88
        let mut a_r = vec![0u128; 512];
        a_r[300] = 1;
        let mut b_r = vec![0u128; 512];
        b_r[300] = 1;

        splitring_mul_setup(&a_r, &b_r)
    }

    #[test]
    fn test_r1cs_splitring_mul_ppw() {
        // Falcon degree = 512, Frog ring of degree 16
        let r1cs =
            SplitNTT::cs_mul(Input::public("a"), Input::public("b"), Input::private("c")).to_r1cs();

        // 5X^10 * 5X^10 = 25X^20
        let (a, b, t, aux) = splitring_mul_setup_0();
        let mut z = Vec::with_capacity(3 * K + K * K + 1); // inputs + constant 1 + aux + output

        // public inputs s, s'
        z.extend(a.splits());
        z.extend(b.splits());

        // constant 1
        z.push(RqNTT::from(1u32));

        // witness (mul result)
        z.extend(t);

        z.extend(aux);

        r1cs.check_relation(&z).unwrap();

        // X^300 * X^300 = -1X^88
        let (a, b, t, aux) = splitring_mul_setup_1();
        let mut z = Vec::with_capacity(3 * K + K * K + 1); // inputs + constant 1 + aux + output

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
        let r1cs = SplitNTT::cs_mul(Input::private("a"), Input::private("b"), Input::public("c"))
            .to_r1cs();
        let (a, b, t, aux) = splitring_mul_setup_0();
        let mut z = Vec::with_capacity(3 * K + K * K + 1); // inputs + constant 1 + aux + output

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
        let r1cs =
            SplitNTT::cs_mul(Input::private("a"), Input::public("b"), Input::public("c")).to_r1cs();
        let (a, b, t, aux) = splitring_mul_setup_0();
        let mut z = Vec::with_capacity(3 * K + K * K + 1); // inputs + constant 1 + aux + output

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
        let r1cs = SplitNTT::cs_mul(Input::private("a"), Input::public("b"), Input::private("c"))
            .to_r1cs();
        let (a, b, t, aux) = splitring_mul_setup_0();
        let mut z = Vec::with_capacity(3 * K + K * K + 1); // inputs + constant 1 + aux + output

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
        let r1cs = RqNTT::cs_norm_bound(Input::public("a"), d, bound).to_r1cs();

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
    fn test_r1cs_ring_norm_bound_xy() {
        let mut rng = rand::thread_rng();
        let bound = 16; // 2^16
        let d = 512;
        let r1cs =
            RqNTT::cs_norm_bound_xy(Input::public("a"), Input::public("b"), d, bound).to_r1cs();

        let a_r = (0..d).map(|_| rng.gen_range(0..10)).collect::<Vec<_>>();
        let b_r = (0..d).map(|_| rng.gen_range(0..10)).collect::<Vec<_>>();

        let norm_a: u128 = a_r.iter().map(|x| x * x).sum();
        let norm_b: u128 = b_r.iter().map(|x| x * x).sum();
        let total_norm = norm_a + norm_b;

        assert!(total_norm < (1u128 << bound));

        let mut z = Vec::with_capacity(4 * d + 2 + bound);

        z.extend(
            a_r.iter()
                .map(|x| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*x))),
        );
        z.extend(
            b_r.iter()
                .map(|x| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*x))),
        );

        z.push(RqNTT::from(1u32)); // constant 1

        a_r.iter().for_each(|coeff| {
            z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
                coeff * coeff,
            )));
        });

        b_r.iter().for_each(|coeff| {
            z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
                coeff * coeff,
            )));
        });

        z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
            norm_a,
        )));
        z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
            norm_b,
        )));

        let mut remaining = total_norm;
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
        let r1cs = SplitNTT::cs_norm_bound(Input::public("a"), d, bound).to_r1cs();

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
    fn test_r1cs_splitring_norm_bound_xy() {
        let mut rng = rand::thread_rng();
        let bound = 16; // 2^16
        let d = 512;
        let r1cs =
            SplitNTT::cs_norm_bound_xy(Input::public("a"), Input::public("b"), d, bound).to_r1cs();

        let a_r = (0..d).map(|_| rng.gen_range(0..10)).collect::<Vec<_>>();
        let b_r = (0..d).map(|_| rng.gen_range(0..10)).collect::<Vec<_>>();

        let norm_a: u128 = a_r.iter().map(|x| x * x).sum();
        let norm_b: u128 = b_r.iter().map(|x| x * x).sum();
        let total_norm = norm_a + norm_b;

        assert!(total_norm < (1u128 << bound));

        let mut z = Vec::with_capacity(4 * d + 2 + bound);

        // public input poly
        z.extend(
            a_r.iter()
                .map(|x| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*x))),
        );
        z.extend(
            b_r.iter()
                .map(|x| RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(*x))),
        );

        z.push(RqNTT::from(1u32)); // constant 1    

        a_r.iter().for_each(|coeff| {
            z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
                coeff * coeff,
            )));
        });

        b_r.iter().for_each(|coeff| {
            z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
                coeff * coeff,
            )));
        });

        z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
            norm_a,
        )));
        z.push(RqNTT::from_scalar(<RqNTT as PolyRing>::BaseRing::from(
            norm_b,
        )));

        let mut remaining = total_norm;
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
    fn test_r1cs_ring_combine() {
        let r1cs = RqNTT::cs_combine(Input::private("x"), Input::public("coeffs"), 4).to_r1cs();
        let mut x = RqPoly::ZERO;
        x.coeffs_mut()[0] = 10u32.into();
        x.coeffs_mut()[1] = 5u32.into();
        x.coeffs_mut()[3] = 30u32.into();

        let z = &[
            RqNTT::from(10u32),
            RqNTT::from(5u32),
            RqNTT::from(0u32),
            RqNTT::from(30u32),
            RqNTT::ONE,
            x.crt(),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_ring_add_ppw() {
        let r1cs =
            RqNTT::cs_add(Input::public("a"), Input::public("b"), Input::private("c")).to_r1cs();
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
        let r1cs =
            RqNTT::cs_add(Input::private("a"), Input::private("b"), Input::public("c")).to_r1cs();
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
        let r1cs =
            RqNTT::cs_add(Input::private("a"), Input::public("b"), Input::private("c")).to_r1cs();
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
        let r1cs =
            RqNTT::cs_add(Input::private("a"), Input::public("b"), Input::public("c")).to_r1cs();
        // 2+3 = 5
        let z = &[
            RqNTT::from(3u32),
            RqNTT::from(5u32),
            RqNTT::from(1u32),
            RqNTT::from(2u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_splitring_lift_term() {
        let r1cs = SplitNTT::cs_liftsub(
            Input::private("a"),
            Input::public("b"),
            Input::public("c"),
            FALCON_MOD.into(),
        )
        .to_r1cs();

        // 15000X^10 - p*1X^10 = 2711X^10
        let mut a_r = vec![0u128; 512];
        a_r[10] = 15000;
        let mut b_r = vec![0u128; 512];
        b_r[10] = 1;
        let mut c_r = vec![0u128; 512];
        c_r[10] = 2711;

        let a = SplitPoly::from_r(&a_r).crt();
        let b = SplitPoly::from_r(&b_r).crt();
        let c = SplitPoly::from_r(&c_r).crt();

        let mut z = Vec::with_capacity(3 * K + 1); // inputs + constant 1 + output
        z.extend(b.splits());
        z.extend(c.splits());
        z.push(RqNTT::from(1u32));
        z.extend(a.splits());

        r1cs.check_relation(&z).unwrap();
    }
}
