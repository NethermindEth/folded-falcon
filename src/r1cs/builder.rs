use super::CSRing;
use latticefold::arith::r1cs::{ConstraintSystem, R1CS};
use stark_rings_linalg::SparseMatrix;
use std::cmp::Ordering;

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

#[cfg(test)]
mod tests {
    use super::{super::signature_verification_cs, *};
    use cyclotomic_rings::rings::FrogRingNTT as RqNTT;

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
}
