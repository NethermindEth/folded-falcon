use crate::falcon::FalconPoly;
use cyclotomic_rings::rings::SuitableRing;
use num_bigint::BigUint;
use num_traits::ToPrimitive;
use stark_rings::{
    OverField, PolyRing, Ring, balanced_decomposition::convertible_ring::ConvertibleRing,
    cyclotomic_ring::CRT,
};
use std::{
    array,
    ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};

/// A ring R's decomposed representation into `K` subrings S. Elements are in coefficient form.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SplitRingPoly<S: OverField, const K: usize>([S; K]);

/// A ring R's decomposed representation into `K` subrings S. Elements are in NTT form, employable in
/// LatticeFold.
/// This ring representation does not implement `SuitableRing` as some of the traits required do
/// not particularly fit the vector of NTT representations structure, e.g., `OverField`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SplitRing<U: SuitableRing, const K: usize>([U; K]);

impl<S: OverField, const K: usize> SplitRingPoly<S, K> {
    /// Maps an element from ring R of degree d*k to k elements in subring S of degree d
    ///
    /// Bijection ϕ: R → S^k where:
    /// r = ∑(i=0 to k-1) si(X^k) ⊗_R X^i
    ///
    /// Assumes mod of S >> mod of R (if R has modulus)
    /// Assumes mod of R < 2^128
    pub fn from_r(r_coeffs: &[impl Into<u128> + Copy]) -> Self {
        let dk = r_coeffs.len(); // R degree
        let d = S::dimension(); // S degree
        assert!(d <= dk);
        assert!(dk % d == 0);

        let mut s = [S::from(0u128); K];

        for (g, coeff) in r_coeffs.iter().enumerate() {
            let c: u128 = (*coeff).into();

            let i = g % K;
            let j = g / K;

            s[i].coeffs_mut()[j] = S::BaseRing::from(c);
        }

        Self(s)
    }

    /// Creates `Self` from a [`FalconPoly`]
    pub fn from_fpoly<const N: usize>(p: &FalconPoly<N>) -> Self {
        Self::from_r(p.coeffs())
    }

    /// Maps back subrings S to a ring R
    pub fn recompose(&self) -> Vec<u128>
    where
        S::BaseRing: ConvertibleRing,
    {
        let d = S::dimension();
        let dk = d * K;

        let mut r = vec![0u128; dk];

        self.0.iter().enumerate().for_each(|(i, s_i)| {
            s_i.coeffs().iter().enumerate().for_each(|(j, c)| {
                let g = j * K + i;
                let bi: BigUint =
                    Into::<<S::BaseRing as ConvertibleRing>::UnsignedInt>::into(*c).into();
                r[g] = bi.to_u128().unwrap();
            });
        });

        r
    }

    /// Converts self's coefficient form into its NTT form
    pub fn crt<U: SuitableRing<CoefficientRepresentation = S>>(&self) -> SplitRing<U, K>
    where
        S: CRT<CRTForm = U>,
    {
        SplitRing(array::from_fn(|i| self.splits()[i].crt()))
    }

    /// Calculates a lifting polynomial `v`, where `self mod p` is lifted to `self + v*p mod q`
    pub fn lift(&self, p: impl Into<u128>) -> Self
    where
        S::BaseRing: ConvertibleRing,
    {
        let p: u128 = p.into();
        let mid = <S::BaseRing as ConvertibleRing>::UnsignedInt::from(u128::from(<<S::BaseRing as ark_ff::Field>::BasePrimeField as ark_ff::PrimeField>::MODULUS_MINUS_ONE_DIV_TWO.as_ref()[0]));
        let q = u128::from(
            <<S::BaseRing as ark_ff::Field>::BasePrimeField as ark_ff::PrimeField>::MODULUS
                .as_ref()[0],
        );
        let p = <S::BaseRing as ConvertibleRing>::UnsignedInt::from(p);
        let qm1 = <S::BaseRing as ConvertibleRing>::UnsignedInt::from(q) - 1.into();
        let v: Vec<S> = self
            .splits()
            .iter()
            .map(|split| {
                split
                    .coeffs()
                    .iter()
                    .map(|c| {
                        let c_int = Into::<<S::BaseRing as ConvertibleRing>::UnsignedInt>::into(*c);
                        if c_int > mid {
                            -S::BaseRing::from((qm1.clone() - c_int) / p.clone() + 1.into())
                        } else {
                            S::BaseRing::from(c_int / p.clone())
                        }
                    })
                    .collect::<Vec<_>>()
                    .into()
            })
            .collect::<Vec<_>>();
        Self(v.try_into().unwrap())
    }

    /// Centers self coefficients to [-p/2, p/2] around the self's modulus
    pub fn center(&mut self, p: impl Into<u128>)
    where
        S::BaseRing: ConvertibleRing,
    {
        let p: u128 = p.into();
        let half_p = <S::BaseRing as ConvertibleRing>::UnsignedInt::from(p / 2);
        let p = <S::BaseRing as ConvertibleRing>::UnsignedInt::from(p);
        self.0.iter_mut().for_each(|split| {
            split.coeffs_mut().iter_mut().for_each(|c| {
                let c_int = Into::<<S::BaseRing as ConvertibleRing>::UnsignedInt>::into(*c);
                if c_int > half_p {
                    *c = -S::BaseRing::from(p.clone() - c_int);
                }
            })
        });
    }

    /// Returns the inner subrings, consuming `self`
    pub fn into_array(self) -> [S; K] {
        self.0
    }

    /// Returns a reference to the inner subrings
    pub fn splits(&self) -> &[S] {
        &self.0
    }
}

impl<U: SuitableRing, const K: usize> SplitRing<U, K> {
    /// Converts self's coefficient form into its NTT form
    pub fn icrt(&self) -> SplitRingPoly<U::CoefficientRepresentation, K> {
        SplitRingPoly(array::from_fn(|i| self.splits()[i].icrt()))
    }

    /// Returns a reference to the inner subrings
    pub fn splits(&self) -> &[U] {
        &self.0
    }

    /// Returns the inner subrings, consuming `self`
    pub fn into_array(self) -> [U; K] {
        self.0
    }
}

impl<S: OverField, const K: usize> AddAssign for SplitRingPoly<S, K> {
    fn add_assign(&mut self, rhs: Self) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a_i, b_i)| *a_i += b_i);
    }
}

impl<S: OverField, const K: usize> Add for SplitRingPoly<S, K> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<S: OverField, const K: usize> SubAssign for SplitRingPoly<S, K> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a_i, b_i)| *a_i -= b_i);
    }
}

impl<S: OverField, const K: usize> Sub for SplitRingPoly<S, K> {
    type Output = Self;
    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<S: OverField, const K: usize> MulAssign for SplitRingPoly<S, K> {
    fn mul_assign(&mut self, rhs: Self) {
        let mut t = [S::ZERO; K];
        for i in 0..K {
            if self.0[i].is_zero() {
                continue;
            }
            for j in 0..K {
                if rhs.0[j].is_zero() {
                    continue;
                }

                let l = (i + j) % K;
                let w = (i + j) / K;
                let mut x = S::ZERO;
                x.coeffs_mut()[w] = 1u32.into();
                t[l] += self.0[i] * rhs.0[j] * x;
            }
        }

        *self = Self(t);
    }
}

impl<S: OverField, const K: usize> Mul for SplitRingPoly<S, K> {
    type Output = Self;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<S: OverField + for<'a> MulAssign<&'a u128>, const K: usize> MulAssign<&u128>
    for SplitRingPoly<S, K>
{
    fn mul_assign(&mut self, rhs: &u128) {
        self.0.iter_mut().for_each(|s_i| *s_i *= rhs);
    }
}

impl<S: OverField + for<'a> MulAssign<&'a u128>, const K: usize> Mul<&u128>
    for SplitRingPoly<S, K>
{
    type Output = Self;

    fn mul(mut self, rhs: &u128) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<S: OverField + for<'a> MulAssign<&'a u16>, const K: usize> MulAssign<&u16>
    for SplitRingPoly<S, K>
{
    fn mul_assign(&mut self, rhs: &u16) {
        self.0.iter_mut().for_each(|s_i| *s_i *= rhs);
    }
}

impl<S: OverField + for<'a> MulAssign<&'a u16>, const K: usize> Mul<&u16> for SplitRingPoly<S, K> {
    type Output = Self;

    fn mul(mut self, rhs: &u16) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<U: SuitableRing, const K: usize> Mul for SplitRing<U, K> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let k = self.0.len();

        let mut t = [U::ZERO; K];

        for i in 0..k {
            if self.0[i].is_zero() {
                continue;
            }
            for j in 0..k {
                if rhs.0[j].is_zero() {
                    continue;
                }

                let l = (i + j) % k;
                let w = (i + j) / k;
                let mut x = U::CoefficientRepresentation::ZERO;
                x.coeffs_mut()[w] = 1u32.into();
                t[l] += self.0[i] * rhs.0[j] * x.crt();
            }
        }

        Self(t)
    }
}

impl<U: SuitableRing, const K: usize> MulAssign for SplitRing<U, K> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<U: SuitableRing, const K: usize> MulAssign<&u128> for SplitRing<U, K> {
    fn mul_assign(&mut self, rhs: &u128) {
        self.0.iter_mut().for_each(|s_i| *s_i *= rhs);
    }
}

impl<U: SuitableRing, const K: usize> Mul<&u128> for SplitRing<U, K> {
    type Output = Self;

    fn mul(mut self, rhs: &u128) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<U: SuitableRing, const K: usize> MulAssign<&u16> for SplitRing<U, K> {
    fn mul_assign(&mut self, rhs: &u16) {
        self.0
            .iter_mut()
            .for_each(|s_i| *s_i *= &(u128::from(*rhs)));
    }
}

impl<U: SuitableRing, const K: usize> Mul<&u16> for SplitRing<U, K> {
    type Output = Self;

    fn mul(mut self, rhs: &u16) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<U: SuitableRing, const K: usize> std::ops::Index<usize> for SplitRing<U, K> {
    type Output = U;

    fn index(&self, index: usize) -> &U {
        &self.0[index]
    }
}

impl<U: SuitableRing, const K: usize> AddAssign for SplitRing<U, K> {
    fn add_assign(&mut self, rhs: Self) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a_i, b_i)| *a_i += b_i);
    }
}

impl<U: SuitableRing, const K: usize> Add for SplitRing<U, K> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<U: SuitableRing, const K: usize> SubAssign for SplitRing<U, K> {
    fn sub_assign(&mut self, rhs: Self) {
        self.0
            .iter_mut()
            .zip(rhs.0.iter())
            .for_each(|(a_i, b_i)| *a_i -= b_i);
    }
}

impl<U: SuitableRing, const K: usize> Sub for SplitRing<U, K> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::falcon::FALCON_MOD;

    use ark_ff::fields::PrimeField;
    use cyclotomic_rings::rings::FrogRingPoly as Poly;
    use stark_rings::PolyRing;
    use stark_rings::cyclotomic_ring::models::frog_ring::Fq;

    const K: usize = 32;
    type SplitPoly = SplitRingPoly<Poly, K>;

    #[test]
    fn test_subring_decompose() {
        // r(X) = 3X^100 + 7X^50 + 5X^10 + 4
        let mut r = vec![0u128; 512];
        r[100] = 3;
        r[50] = 7;
        r[10] = 5;
        r[0] = 4;

        let s = SplitPoly::from_r(&r);

        // 4 -> 4 (0)
        // 5X^10 -> 5 (10)
        // 7X^50 -> 7X (18)
        // 3X^100 -> 3X^3 (4)
        let mut expected = [Poly::ZERO; K];
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

        let s = SplitPoly::from_r(&r);
        let recomposed = s.recompose();

        assert_eq!(r, recomposed);
    }

    #[test]
    fn test_splitring_poly_add() {
        // 5X^10 + 5X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 5;

        // expected 5X^10 -> s_10 = 5
        let s1 = SplitPoly::from_r(&r1);
        let s2 = SplitPoly::from_r(&r2);

        let sm = s1 + s2;
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 10X^10
        expected[10] = 10;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_splitring_poly_sub() {
        // 7X^10 - 5X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 7;
        let mut r2 = vec![0u128; 512];
        r2[10] = 5;

        let s1 = SplitPoly::from_r(&r1);
        let s2 = SplitPoly::from_r(&r2);

        let sm = s1 - s2;
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 2X^10
        expected[10] = 2;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_splitring_poly_mul() {
        // 5X^10 * 5X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 5;

        let s1 = SplitPoly::from_r(&r1);
        let s2 = SplitPoly::from_r(&r2);

        let sm = s1 * s2;
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 25X^20
        expected[20] = 25;

        assert_eq!(rm, expected);

        // X^300 * X^300
        let mut r3 = vec![0u128; 512];
        r3[300] = 1;
        let mut r4 = vec![0u128; 512];
        r4[300] = 1;

        let s3 = SplitPoly::from_r(&r3);
        let s4 = SplitPoly::from_r(&r4);

        let sm2 = s3 * s4;
        let rm2 = sm2.recompose();

        let mut expected2 = vec![0u128; 512];
        // -1X^88
        expected2[88] = u128::from(Fq::MODULUS.as_ref()[0]) - 1;

        assert_eq!(rm2, expected2);

        // (2X^5 + 3X^20 + 7X^100) * (4X^15 + 5X^50 + 6X^200)
        let mut r5 = vec![0u128; 512];
        r5[5] = 2;
        r5[20] = 3;
        r5[100] = 7;

        let mut r6 = vec![0u128; 512];
        r6[15] = 4;
        r6[50] = 5;
        r6[200] = 6;

        let s5 = SplitPoly::from_r(&r5);
        let s6 = SplitPoly::from_r(&r6);

        let sm3 = s5 * s6;
        let rm3 = sm3.recompose();

        let mut expected3 = vec![0u128; 512];
        // 8X^20 +12X^35 +10X^55 +15X^70 +28X^115 +12X^205 +18X^220 +35X^150 +42X^300
        expected3[20] = 8;
        expected3[35] = 12;
        expected3[55] = 10;
        expected3[70] = 15;
        expected3[115] = 28;
        expected3[205] = 12;
        expected3[220] = 18;
        expected3[150] = 35;
        expected3[300] = 42;
        assert_eq!(rm3, expected3);
    }

    #[test]
    fn test_splitring_ntt_mul() {
        // 5X^10 * 5X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 5;

        let u1 = SplitPoly::from_r(&r1).crt();
        let u2 = SplitPoly::from_r(&r2).crt();

        let um = u1 * u2;
        let sm = um.icrt();
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 25X^20
        expected[20] = 25;

        assert_eq!(rm, expected);

        // X^300 * X^300 = X^600 % X^512 = X^88
        let mut r3 = vec![0u128; 512];
        r3[300] = 1;
        let mut r4 = vec![0u128; 512];
        r4[300] = 1;

        let u3 = SplitPoly::from_r(&r3).crt();
        let u4 = SplitPoly::from_r(&r4).crt();

        let um2 = u3 * u4;
        let sm2 = um2.icrt();
        let rm2 = sm2.recompose();

        let mut expected2 = vec![0u128; 512];
        expected2[88] = u128::from(Fq::MODULUS.as_ref()[0]) - 1;

        assert_eq!(rm2, expected2);

        // (2X^5 + 3X^20 + 7X^100) * (4X^15 + 5X^50 + 6X^200)
        let mut r5 = vec![0u128; 512];
        r5[5] = 2;
        r5[20] = 3;
        r5[100] = 7;

        let mut r6 = vec![0u128; 512];
        r6[15] = 4;
        r6[50] = 5;
        r6[200] = 6;

        let s5 = SplitPoly::from_r(&r5);
        let s6 = SplitPoly::from_r(&r6);

        let u5 = s5.crt();
        let u6 = s6.crt();

        let um3 = u5 * u6;
        let sm3 = um3.icrt();
        let rm3 = sm3.recompose();

        let mut expected3 = vec![0u128; 512];
        expected3[20] = 8;
        expected3[35] = 12;
        expected3[55] = 10;
        expected3[70] = 15;
        expected3[115] = 28;
        expected3[150] = 35;
        expected3[205] = 12;
        expected3[220] = 18;
        expected3[300] = 42;

        assert_eq!(rm3, expected3);
    }

    #[test]
    fn test_splitring_ntt_add() {
        // 5X^10 + 3X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 3;

        let s1 = SplitPoly::from_r(&r1).crt();
        let s2 = SplitPoly::from_r(&r2).crt();

        let sm_ntt = s1 + s2;
        let sm = sm_ntt.icrt();
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 8X^10
        expected[10] = 8;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_splitring_ntt_sub() {
        // 5X^10 - 3X^10
        let mut r1 = vec![0u128; 512];
        r1[10] = 5;
        let mut r2 = vec![0u128; 512];
        r2[10] = 3;

        let s1 = SplitPoly::from_r(&r1).crt();
        let s2 = SplitPoly::from_r(&r2).crt();

        let sm_ntt = s1 - s2;
        let sm = sm_ntt.icrt();
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        // 2X^10
        expected[10] = 2;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_splitring_poly_lift() {
        // 5X^3 + 3000*X^10 * 5X^10 = (5X^3 + 2711^20) mod p
        // 5X^3 + 3000*X^10 * 5X^10 = (5X^3 + 15000X^20) mod q
        // 5X^3 + 3000*X^10 * 5X^10 + pv = (5X^3 + 2711^20) mod q
        let mut s1 = vec![0u128; 512];
        s1[3] = 5;
        let mut s2 = vec![0u128; 512];
        s2[10] = 3000;
        let mut h = vec![0u128; 512];
        h[10] = 5;
        let mut c = vec![0u128; 512];
        c[3] = 5;
        c[20] = 15000;
        let mut v = vec![0u128; 512];
        v[20] = 1;

        let s1 = SplitPoly::from_r(&s1);
        let s2 = SplitPoly::from_r(&s2);
        let h = SplitPoly::from_r(&h);
        let c = SplitPoly::from_r(&c);
        let v = c.lift(FALCON_MOD);

        let sm = s1 + s2 * h - v * &FALCON_MOD;
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        expected[3] = 5;
        expected[20] = 2711;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_splitring_ntt_lift() {
        // 5X^3 + 3000*X^10 * 5X^10 = (5X^3 + 2711^20) mod p
        // 5X^3 + 3000*X^10 * 5X^10 = (5X^3 + 15000X^20) mod q
        // 5X^3 + 3000*X^10 * 5X^10 + pv = (5X^3 + 2711^20) mod q
        let mut s1 = vec![0u128; 512];
        s1[3] = 5;
        let mut s2 = vec![0u128; 512];
        s2[10] = 3000;
        let mut h = vec![0u128; 512];
        h[10] = 5;
        let mut c = vec![0u128; 512];
        c[3] = 5;
        c[20] = 15000;
        let mut v = vec![0u128; 512];
        v[20] = 1;

        let s1 = SplitPoly::from_r(&s1).crt();
        let s2 = SplitPoly::from_r(&s2).crt();
        let h = SplitPoly::from_r(&h).crt();
        let c = SplitPoly::from_r(&c);
        let v = c.lift(FALCON_MOD).crt();

        let sm = s1 + s2 * h - v * &FALCON_MOD;
        let rm = sm.icrt().recompose();

        let mut expected = vec![0u128; 512];
        expected[3] = 5;
        expected[20] = 2711;

        assert_eq!(rm, expected);
    }

    #[test]
    fn test_splitring_poly_center() {
        // 5X^3 + 8000*X^10 * 5X^10 = (5X^3 + 3133^20) mod p
        // 5X^3 + 8000*X^10 * 5X^10 = (5X^3 + 40000^20) mod q
        // 5X^3 + 8000*X^10 * 5X^10 + pv = (5X^3 + 3133^20) mod q
        let mut s1 = vec![0u128; 512];
        s1[3] = 5;
        let mut s2 = vec![0u128; 512];
        s2[10] = 8000;
        let mut h = vec![0u128; 512];
        h[10] = 5;
        let mut c = vec![0u128; 512];
        c[3] = 5;
        c[20] = 40000;
        let mut v = vec![0u128; 512];
        v[20] = 1;

        let s1 = SplitPoly::from_r(&s1);
        let mut s2 = SplitPoly::from_r(&s2);
        s2.center(FALCON_MOD);

        let s2_rec = s2.recompose();
        assert_eq!(
            s2_rec[10],
            u128::from(Fq::MODULUS.as_ref()[0]) - u128::from(FALCON_MOD - 8000)
        );

        let h = SplitPoly::from_r(&h);
        let s1ps2h = s1 + s2 * h;
        let v = s1ps2h.lift(FALCON_MOD);

        let sm = s1ps2h - v * &FALCON_MOD;
        let rm = sm.recompose();

        let mut expected = vec![0u128; 512];
        expected[3] = 5;
        expected[20] = 3133;

        assert_eq!(rm, expected);
    }
}
