use super::CSRing;
use latticefold::arith::r1cs::{ConstraintSystem, R1CS, VariableMap};
use stark_rings_linalg::SparseMatrix;
use std::collections::{HashMap, HashSet};

/// Combine multiple constraint systems into a single [`R1CS`] instance
pub struct R1CSBuilder<R: CSRing> {
    pub systems: Vec<ConstraintSystem<R::Base>>,
}

impl<R: CSRing> R1CSBuilder<R> {
    /// Create an empty builder.
    pub fn new() -> R1CSBuilder<R> {
        Self { systems: vec![] }
    }

    /// Add a [`ConstraintSystem`] to be merged.
    pub fn push(&mut self, cs: ConstraintSystem<R::Base>) {
        self.systems.push(cs);
    }

    /// Merges pushed constraint systems into a single [`R1CS`] instance.
    /// A [`VariableMap`] is also returned containing the indices of the re-mapped variables.
    pub fn build(self) -> (R1CS<R::Base>, VariableMap) {
        let nconstraints = self.systems.iter().map(|s| s.nconstraints()).sum();
        let (input_len, witness_len) = self.count_vars();
        let nvars = input_len + 1 + witness_len; // z = (x || 1 || w)

        let mut a = Self::create_sparse_matrix(nconstraints, nvars);
        let mut b = Self::create_sparse_matrix(nconstraints, nvars);
        let mut c = Self::create_sparse_matrix(nconstraints, nvars);

        let map = self.map_vars();

        // Combine systems, with mapped variables
        let mut offset = 0;
        let one_offset = input_len;
        for system in self.systems.iter() {
            for (i, constraint) in system.constraints.iter().enumerate() {
                let row = i + offset;

                for &(v, index) in &constraint.a.terms {
                    let mapped_index = Self::map_index(system, index, &map, one_offset);
                    a.coeffs[row].push((v, mapped_index));
                }
                for &(v, index) in &constraint.b.terms {
                    let mapped_index = Self::map_index(system, index, &map, one_offset);
                    b.coeffs[row].push((v, mapped_index));
                }
                for &(v, index) in &constraint.c.terms {
                    let mapped_index = Self::map_index(system, index, &map, one_offset);
                    c.coeffs[row].push((v, mapped_index));
                }
            }

            offset += system.nconstraints();
        }

        (
            R1CS {
                l: input_len,
                A: a,
                B: b,
                C: c,
            },
            map,
        )
    }

    /// Creates a new sparse matrix with the given dimensions
    fn create_sparse_matrix(n_rows: usize, n_cols: usize) -> SparseMatrix<R::Base> {
        SparseMatrix {
            n_rows,
            n_cols,
            coeffs: vec![vec![]; n_rows],
        }
    }

    /// Counts the total number of variables and their types (input vs witness)
    fn count_vars(&self) -> (usize, usize) {
        let mut unique_vars = HashMap::new();
        let mut input_len = 0;
        let mut witness_len = 0;

        // Count input vars
        for system in self.systems.iter() {
            for (name, (index, len)) in system.vars.vars() {
                if !unique_vars.contains_key(name) && *index < system.ninputs {
                    unique_vars.insert(name.clone(), (index, len));
                    input_len += *len;
                }
            }
        }

        // Count witness vars
        for system in self.systems.iter() {
            for (name, (index, len)) in system.vars.vars() {
                if !unique_vars.contains_key(name) && *index > system.ninputs {
                    unique_vars.insert(name.clone(), (index, len));
                    witness_len += *len;
                }
            }
        }

        (input_len, witness_len)
    }

    /// Maps variables to their new positions in the combined system
    fn map_vars(&self) -> VariableMap {
        let mut map = VariableMap::new();
        let mut seen_vars = HashSet::new();
        let mut offset = 0;

        // Map public input vars
        for system in self.systems.iter() {
            for (name, (index, len)) in system.vars.vars() {
                if *index < system.ninputs && !seen_vars.contains(name) {
                    seen_vars.insert(name.clone());
                    map.add(name.clone(), offset, *len);
                    offset += *len;
                }
            }
        }

        map.add_one(offset);
        offset += 1;

        // Map witness vars
        for system in self.systems.iter() {
            for (name, (index, len)) in system.vars.vars() {
                if *index > system.ninputs && !seen_vars.contains(name) {
                    seen_vars.insert(name.clone());
                    map.add(name.clone(), offset, *len);
                    offset += len;
                }
            }
        }

        map
    }

    /// Maps a variable index from the original system to its new position
    fn map_index(
        system: &ConstraintSystem<R::Base>,
        index: usize,
        map: &VariableMap,
        one_offset: usize,
    ) -> usize {
        if index == system.ninputs {
            one_offset
        } else {
            let (name, (start_idx, _)) = system
                .vars
                .vars()
                .find(|(_, (idx, len))| *idx <= index && index < *idx + *len)
                .expect("Failed to map input variable index");

            let offset = index - start_idx;
            map.get(name).unwrap().0 + offset
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
    use super::{super::Input, *};
    use cyclotomic_rings::rings::FrogRingNTT as RqNTT;

    #[test]
    fn test_r1cs_composite_ring_mul_double_abc_uvw() {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("b"),
            Input::private("c"),
            0,
        ));
        builder.push(RqNTT::cs_mul(
            Input::public("u"),
            Input::public("v"),
            Input::private("w"),
            0,
        ));
        let (r1cs, _) = builder.build();

        // 2*3 = 6
        // 5*10 = 50
        let z = &[
            RqNTT::from(2u32),
            RqNTT::from(3u32),
            RqNTT::from(5u32),
            RqNTT::from(10u32),
            RqNTT::from(1u32), // one
            RqNTT::from(6u32),
            RqNTT::from(50u32),
        ];
        r1cs.check_relation(z).unwrap();
    }

    #[test]
    fn test_r1cs_composite_ring_mul_double_abc_avw() {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("b"),
            Input::private("c"),
            0,
        ));
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("v"),
            Input::private("w"),
            0,
        ));
        let (r1cs, map) = builder.build();

        let nvars = map.vars().len() + 1;

        let mut z = vec![RqNTT::from(0u32); nvars];
        z[map.get("a").unwrap().0] = RqNTT::from(2u32);
        z[map.get("b").unwrap().0] = RqNTT::from(3u32);
        z[map.get("c").unwrap().0] = RqNTT::from(6u32);
        z[map.get("v").unwrap().0] = RqNTT::from(10u32);
        z[map.get("w").unwrap().0] = RqNTT::from(20u32);
        z[map.get_one()] = RqNTT::from(1u32);

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_composite_ring_mul_double_abf_fvw() {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("b"),
            Input::private("f"),
            0,
        ));
        builder.push(RqNTT::cs_mul(
            Input::private("f"),
            Input::public("v"),
            Input::private("w"),
            0,
        ));
        let (r1cs, map) = builder.build();

        let nvars = map.vars().len() + 1;
        let mut z = vec![RqNTT::from(0u32); nvars];
        z[map.get("a").unwrap().0] = RqNTT::from(2u32);
        z[map.get("b").unwrap().0] = RqNTT::from(3u32);
        z[map.get("f").unwrap().0] = RqNTT::from(6u32);
        z[map.get("v").unwrap().0] = RqNTT::from(10u32);
        z[map.get("w").unwrap().0] = RqNTT::from(60u32);
        z[map.get_one()] = RqNTT::from(1u32);

        r1cs.check_relation(&z).unwrap();
    }

    #[test]
    fn test_r1cs_composite_ring_mul_double_pabf_fvw() {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::private("a"),
            Input::public("b"),
            Input::private("f"),
            0,
        ));
        builder.push(RqNTT::cs_mul(
            Input::private("f"),
            Input::public("v"),
            Input::private("w"),
            0,
        ));
        let (r1cs, map) = builder.build();

        let nvars = map.vars().len() + 1;
        let mut z = vec![RqNTT::from(0u32); nvars];
        z[map.get("a").unwrap().0] = RqNTT::from(2u32);
        z[map.get("b").unwrap().0] = RqNTT::from(3u32);
        z[map.get("f").unwrap().0] = RqNTT::from(6u32);
        z[map.get("v").unwrap().0] = RqNTT::from(10u32);
        z[map.get("w").unwrap().0] = RqNTT::from(60u32);
        z[map.get_one()] = RqNTT::from(1u32);

        r1cs.check_relation(&z).unwrap();
    }
}
