use super::CSRing;
use latticefold::arith::r1cs::{ConstraintSystem, R1CS, VariableMap};
use stark_rings::Ring;
use stark_rings_linalg::SparseMatrix;
use std::collections::{HashMap, HashSet};

/// Combine multiple constraint systems into a single [`R1CS`] instance
pub struct R1CSBuilder<R: CSRing> {
    systems: Vec<ConstraintSystem<R::Base>>,
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

        map.set_one(offset);
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

/// Helper build the `z` vector
#[derive(Clone, Debug)]
pub struct ZBuilder<R: CSRing> {
    map: VariableMap,
    set: HashSet<String>,
    z: Vec<R::Base>,
}

/// Possible errors on building the `z` vector by [`ZBuilder`]
#[derive(Clone, Debug, thiserror::Error)]
pub enum ZBuildError {
    /// Expected variable length different than that provided
    #[error("unexpected length {1} for variable {0}: expected {2} length")]
    LengthMismatch(String, usize, usize),
    /// Variable was already assigned
    #[error("variable {0} already set")]
    AlreadySet(String),
    /// Variable does not exist
    #[error("variable {0} not found")]
    NotFound(String),
    /// Some variables were not assigned
    #[error("some variables not set: {0:?}")]
    VariablesNotSet(Vec<String>),
}

impl<R: CSRing> ZBuilder<R> {
    /// Create a new builder, using a variable map as context.
    pub fn new(map: VariableMap) -> Self {
        let total_len = map.total_len();
        let one_index = map.get_one();
        let mut z = vec![R::Base::ZERO; total_len];
        z[one_index] = R::Base::ONE;
        Self {
            map,
            set: HashSet::new(),
            z,
        }
    }

    /// Set a variable's value.
    pub fn set(&mut self, name: &str, val: &[R::Base]) -> Result<&mut Self, ZBuildError> {
        if self.set.contains(name) {
            return Err(ZBuildError::AlreadySet(name.into()));
        }
        if let Some((index, len)) = self.map.get(name) {
            if len != val.len() {
                return Err(ZBuildError::LengthMismatch(name.into(), val.len(), len));
            }
            self.set.insert(name.into());
            self.z[index..index + len].copy_from_slice(val);
        } else {
            return Err(ZBuildError::NotFound(name.into()));
        }
        Ok(self)
    }

    /// Fetch the currently built `z` vector. This `ZBuilder` instance can then be reused to build
    /// another `z`.
    pub fn build(&mut self) -> Result<Vec<R::Base>, ZBuildError> {
        let unset = self
            .map
            .vars()
            .filter(|(name, _)| !self.set.contains(name.as_str()))
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>();
        if !unset.is_empty() {
            return Err(ZBuildError::VariablesNotSet(unset));
        }
        self.set.clear();
        Ok(std::mem::take(&mut self.z))
    }
}

#[cfg(test)]
mod tests {
    use super::{super::Input, *};
    use anyhow::Result;
    use cyclotomic_rings::rings::FrogRingNTT as RqNTT;

    #[test]
    fn test_r1cs_builder_ring_mul_double_abc_uvw() -> Result<()> {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("b"),
            Input::private("c"),
        ));
        builder.push(RqNTT::cs_mul(
            Input::public("u"),
            Input::public("v"),
            Input::private("w"),
        ));
        let (r1cs, map) = builder.build();

        // 2*3 = 6
        // 5*10 = 50
        let z = ZBuilder::<RqNTT>::new(map)
            .set("a", &[2u32.into()])?
            .set("b", &[3u32.into()])?
            .set("c", &[6u32.into()])?
            .set("u", &[5u32.into()])?
            .set("v", &[10u32.into()])?
            .set("w", &[50u32.into()])?
            .build()?;

        r1cs.check_relation(&z)?;

        Ok(())
    }

    #[test]
    fn test_r1cs_builder_ring_mul_double_abc_avw() -> Result<()> {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("b"),
            Input::private("c"),
        ));
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("v"),
            Input::private("w"),
        ));
        let (r1cs, map) = builder.build();

        let z = ZBuilder::<RqNTT>::new(map)
            .set("a", &[2u32.into()])?
            .set("b", &[3u32.into()])?
            .set("c", &[6u32.into()])?
            .set("v", &[10u32.into()])?
            .set("w", &[20u32.into()])?
            .build()?;

        r1cs.check_relation(&z)?;

        Ok(())
    }

    #[test]
    fn test_r1cs_builder_ring_mul_double_abf_fvw() -> Result<()> {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::public("a"),
            Input::public("b"),
            Input::private("f"),
        ));
        builder.push(RqNTT::cs_mul(
            Input::private("f"),
            Input::public("v"),
            Input::private("w"),
        ));
        let (r1cs, map) = builder.build();

        let z = ZBuilder::<RqNTT>::new(map)
            .set("a", &[2u32.into()])?
            .set("b", &[3u32.into()])?
            .set("f", &[6u32.into()])?
            .set("v", &[10u32.into()])?
            .set("w", &[60u32.into()])?
            .build()?;

        r1cs.check_relation(&z)?;

        Ok(())
    }

    #[test]
    fn test_r1cs_builder_ring_mul_double_pabf_fvw() -> Result<()> {
        let mut builder = R1CSBuilder::<RqNTT>::new();
        builder.push(RqNTT::cs_mul(
            Input::private("a"),
            Input::public("b"),
            Input::private("f"),
        ));
        builder.push(RqNTT::cs_mul(
            Input::private("f"),
            Input::public("v"),
            Input::private("w"),
        ));
        let (r1cs, map) = builder.build();

        let z = ZBuilder::<RqNTT>::new(map)
            .set("a", &[2u32.into()])?
            .set("b", &[3u32.into()])?
            .set("f", &[6u32.into()])?
            .set("v", &[10u32.into()])?
            .set("w", &[60u32.into()])?
            .build()?;

        r1cs.check_relation(&z)?;

        Ok(())
    }
}
