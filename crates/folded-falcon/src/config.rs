use crate::{
    FalconInput, FalconSig,
    falcon::{Falcon512, Falcon1024, FalconOps, FalconParams},
    r1cs::{CSRing, ConstraintScheme, ZBuildError},
    subring::SplitRing,
};
use cyclotomic_rings::rings::FrogRingNTT;
use latticefold::arith::r1cs::{R1CS, VariableMap};

/// A compatible ring for LatticeFold'ed Falcon signatures.
pub trait FoldedRing {
    type Ring: ConstraintScheme;
    type Variant: FalconOps;

    fn r1cs(n: usize) -> (R1CS<<Self::Ring as CSRing>::Base>, VariableMap) {
        Self::Ring::r1cs(n, Self::Variant::N, Self::Variant::LSB2)
    }

    fn z<const N: usize>(
        xw: &[(FalconInput<N>, FalconSig<N>)],
        map: VariableMap,
    ) -> Result<Vec<<Self::Ring as CSRing>::Base>, ZBuildError> {
        Self::Ring::z(xw, map, Self::Variant::LSB2)
    }
}

pub struct F512Frog16 {}
impl FoldedRing for F512Frog16 {
    type Ring = SplitRing<FrogRingNTT, 32>;
    type Variant = Falcon512;
}

pub struct F1024Frog16 {}
impl FoldedRing for F1024Frog16 {
    type Ring = SplitRing<FrogRingNTT, 64>;
    type Variant = Falcon1024;
}
