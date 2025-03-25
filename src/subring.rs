use cyclotomic_rings::rings::SuitableRing;
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use stark_rings::{
    PolyRing,
    balanced_decomposition::convertible_ring::ConvertibleRing,
    cyclotomic_ring::{CRT, ICRT},
};
use std::ops::{Add, AddAssign, Mul, MulAssign};

/// A ring R's decomposed representation into subrings S. Elements are in coefficient form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SplitRingPoly<S: PolyRing>(Vec<S>);

/// A ring R's decomposed representation into subrings S. Elements are in NTT form, employable in
/// LatticeFold.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SplitRing<U: SuitableRing>(Vec<U>);

impl<S: PolyRing> SplitRingPoly<S> {
    /// Maps an element from ring R of degree d*k to k elements in subring S of degree d
    ///
    /// Bijection ϕ: R → S^k where:
    /// r = ∑(i=0 to k-1) si(X^k) ⊗_R X^i
    ///
    /// Assumes mod of S >> mod of R (if R has modulus)
    /// Assumes mod of R < 2^128
    pub fn from_r(r_coeffs: &[u128]) -> Self
    where
        S::BaseRing: ConvertibleRing,
    {
        let dk = r_coeffs.len(); // R degree
        let d = S::dimension(); // S degree
        assert!(d <= dk);
        assert!(dk % d == 0);
        let k = dk / d; // Number of subrings

        let mut s = vec![S::from(0u128); k];

        for g in 0..dk {
            if r_coeffs[g] == 0u128 {
                continue;
            }

            let i = g % k;
            let j = g / k;

            s[i].coeffs_mut()[j] += S::BaseRing::from(r_coeffs[g].to_u128().unwrap());
        }

        Self(s)
    }

    /// Maps back subrings S to a ring R
    pub fn recompose(&self) -> Vec<u128>
    where
        S::BaseRing: ConvertibleRing,
    {
        let d = S::dimension();
        let k = self.0.len();
        let dk = d * k;

        let mut r = vec![0u128; dk];

        self.0.iter().enumerate().for_each(|(i, s_i)| {
            s_i.coeffs().iter().enumerate().for_each(|(j, c)| {
                let g = j * k + i;
                let bi: BigUint =
                    Into::<<S::BaseRing as ConvertibleRing>::UnsignedInt>::into(*c).into();
                r[g] += bi.to_u128().unwrap();
            });
        });

        r
    }

    /// Converts self's coefficient form into its NTT form
    pub fn crt<U: SuitableRing<CoefficientRepresentation = S>>(self) -> SplitRing<U>
    where
        S: CRT<CRTForm = U>,
    {
        SplitRing(CRT::elementwise_crt(self.0))
    }
}

impl<U: SuitableRing> SplitRing<U> {
    /// Converts self's coefficient form into its NTT form
    pub fn icrt(self) -> SplitRingPoly<U::CoefficientRepresentation> {
        SplitRingPoly(ICRT::elementwise_icrt(self.0))
    }
}

impl<S: PolyRing> AddAssign for SplitRingPoly<S> {
    fn add_assign(&mut self, rhs: Self) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a_i, b_i)| *a_i += b_i);
    }
}

impl<S: PolyRing> Add for SplitRingPoly<S> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<S: PolyRing> MulAssign for SplitRingPoly<S> {
    fn mul_assign(&mut self, rhs: Self) {
        let k = self.0.len();

        let mut t = vec![S::from(0u128); k];
        for i in 0..k {
            if self.0[i].is_zero() {
                continue;
            }
            for j in 0..k {
                if rhs.0[j].is_zero() {
                    continue;
                }
                let l = (i + j) % k;
                let g = (i + j) / k;
                t[l].coeffs_mut()[g] += self.0[i].coeffs()[g] * rhs.0[j].coeffs()[g];
            }
        }

        *self = Self(t);
    }
}

impl<S: PolyRing> Mul for SplitRingPoly<S> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<U: SuitableRing> Mul for SplitRing<U> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let k = self.0.len();
        let mut t = vec![U::from(0u128); k];

        for i in 0..k {
            if self.0[i].is_zero() {
                continue;
            }
            for j in 0..k {
                if rhs.0[j].is_zero() {
                    continue;
                }
                let l = (i + j) % k;
                t[l] += self.0[i] * rhs.0[j];
            }
        }

        Self(t)
    }
}

impl<U: SuitableRing> MulAssign for SplitRing<U> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use cyclotomic_rings::rings::FrogRingNTT as NTT;
    use cyclotomic_rings::rings::FrogRingPoly as Poly;
    use stark_rings::PolyRing;

    #[test]
    fn test_subring_decompose() {
        // r(X) = 3X^100 + 7X^50 + 5X^10 + 4
        let mut r = vec![0u128; 512];
        r[100] = 3;
        r[50] = 7;
        r[10] = 5;
        r[0] = 4;

        let s = SplitRingPoly::<Poly>::from_r(&r);

        // 4 -> 4 (0)
        // 5X^10 -> 5 (10)
        // 7X^50 -> 7X (18)
        // 3X^100 -> 3X^3 (4)
        let mut expected = vec![Poly::from(0u128); 32];
        expected[0].coeffs_mut()[0] = 4.into();
        expected[10].coeffs_mut()[0] = 5.into();
        expected[18].coeffs_mut()[1] = 7.into();
        expected[4].coeffs_mut()[3] = 3.into();

        assert_eq!(s.0, expected);
    }

    #[test]
    fn test_subring_recompose() {
        let mut r = vec![0u128; 512];
        r[100] = 3;
        r[50] = 7;
        r[10] = 5;
        r[0] = 4;

        let s: SplitRingPoly<Poly> = SplitRingPoly::from_r(&r);
        let recomposed = s.recompose();

        assert_eq!(r, recomposed);
    }

    #[test]
    fn test_subring_add() {
        // 5X^10 * 5X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 5;

        // expected 5X^10 -> s_10 = 5
        let s1: SplitRingPoly<Poly> = SplitRingPoly::from_r(&r1);
        let s2: SplitRingPoly<Poly> = SplitRingPoly::from_r(&r2);

        let sm = s1 + s2;
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 10X^10
        expected[10] = 10;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_subring_mul() {
        // 5X^10 * 5X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 5;

        // expected 5X^10 -> s_10 = 5
        let s1: SplitRingPoly<Poly> = SplitRingPoly::from_r(&r1);
        let s2: SplitRingPoly<Poly> = SplitRingPoly::from_r(&r2);

        let sm = s1 * s2;
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 25X^20
        expected[20] = 25;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_subring_mul_ntt_0() {
        // 5X^10 * 5X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 5;

        // expected 5X^10 -> s_10 = 5
        let u1: SplitRing<NTT> = SplitRingPoly::<Poly>::from_r(&r1).crt();
        let u2: SplitRing<NTT> = SplitRingPoly::<Poly>::from_r(&r2).crt();

        // multiply using NTT
        let um = u1 * u2;
        let sm = um.icrt();
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 25X^20
        expected[20] = 25;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_subring_mul_ntt_1() {
        // 5X^10 * 10X^20
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[20] = 10;

        // 5X^10 -> s_10 = 5
        let u1: SplitRing<NTT> = SplitRingPoly::<Poly>::from_r(&r1).crt();
        // 10X^20 -> s_4 = 10x
        let u2: SplitRing<NTT> = SplitRingPoly::<Poly>::from_r(&r2).crt();

        // multiply using NTT
        let um = u1 * u2;
        let sm = um.icrt();
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 50X^30
        expected[30] = 50;

        assert_eq!(rm, expected);
    }
}
