/// q is 12289, the integer modulus which is used in Falcon.
/// const Q: u32 = 12 * 1024 + 1
///
/// FalconVariant::Falcon512 => FalconParameters {
///     n: 512,
///     sigma: 165.7366171829776,
///     sigmin: 1.2778336969128337,
///     sig_bound: 34034726,
///     sig_bytelen: 666,
/// },
/// FalconVariant::Falcon1024 => FalconParameters {
///     n: 1024,
///     sigma: 168.38857144654395,
///     sigmin: 1.298280334344292,
///     sig_bound: 70265242,
///     sig_bytelen: 1280,
/// },
use crate::{FalconInput, FalconSig};
use falcon_rust::{
    encoding::decompress,
    falcon::{PublicKey, SecretKey, Signature},
    falcon_field::Felt,
    falcon512, falcon1024,
    fast_fft::FastFft,
    polynomial::{Polynomial, hash_to_point},
};
use itertools::Itertools;

pub const FALCON_MOD: u16 = 12289;

pub struct Falcon512;
pub struct Falcon1024;

pub trait FalconOps: FalconParams {
    fn keygen(seed: [u8; 32]) -> (Self::SecretKey, Self::PublicKey);
    fn sign(m: &[u8], sk: &Self::SecretKey) -> Self::Signature;
    fn verify(m: &[u8], sig: &Self::Signature, pk: &Self::PublicKey) -> bool;
    fn deserialize(
        m: &[u8],
        sig: &Self::Signature,
        pk: &Self::PublicKey,
    ) -> (Self::Input, Self::Witness);
}

macro_rules! impl_falcon_ops {
    ($variant:ident, $n:literal) => {
        impl FalconOps for $variant {
            fn keygen(seed: [u8; 32]) -> (SecretKey<$n>, PublicKey<$n>) {
                paste::paste! { [<falcon $n>]::keygen(seed) }
            }
            fn sign(m: &[u8], sk: &SecretKey<$n>) -> Signature<$n> {
                paste::paste! { [<falcon $n>]::sign(m, sk) }
            }
            fn verify(m: &[u8], sig: &Signature<$n>, pk: &PublicKey<$n>) -> bool {
                paste::paste! { [<falcon $n>]::verify(m, sig, pk) }
            }
            fn deserialize(
                m: &[u8],
                sig: &Signature<$n>,
                pk: &PublicKey<$n>,
            ) -> (FalconInput<$n>, FalconSig<$n>) {
                deserialize(m, sig, pk)
            }
        }
    };
}

impl_falcon_ops!(Falcon512, 512);
impl_falcon_ops!(Falcon1024, 1024);

/// Parameters used in each Falcon variant.
/// Also contains associated types for each variant degree (avoid use of `feature(generic_const_exprs)`.
pub trait FalconParams {
    /// Degree
    const N: usize;
    /// log2 of the signature l2-norm bound squared
    const LSB2: usize;
    /// Secret key
    type SecretKey;
    /// Public key
    type PublicKey;
    /// Signature
    type Signature;
    /// Constraint system public input
    type Input;
    /// Constraint system witness
    type Witness;
}

impl FalconParams for Falcon512 {
    const N: usize = 512;
    const LSB2: usize = 26; // log2(34034726)
    type SecretKey = SecretKey<{ Self::N }>;
    type PublicKey = PublicKey<{ Self::N }>;
    type Signature = Signature<{ Self::N }>;
    type Input = FalconInput<{ Self::N }>;
    type Witness = FalconSig<{ Self::N }>;
}

impl FalconParams for Falcon1024 {
    const N: usize = 1024;
    const LSB2: usize = 27; // log2(70265242)
    type SecretKey = SecretKey<{ Self::N }>;
    type PublicKey = PublicKey<{ Self::N }>;
    type Signature = Signature<{ Self::N }>;
    type Input = FalconInput<{ Self::N }>;
    type Witness = FalconSig<{ Self::N }>;
}

fn deserialize<const N: usize>(
    m: &[u8],
    sig: &Signature<N>,
    pk: &PublicKey<N>,
) -> (FalconInput<N>, FalconSig<N>) {
    let r_cat_m = [sig.r.to_vec(), m.to_vec()].concat();
    let c = hash_to_point(&r_cat_m, N);

    let s2 = decompress(&sig.s, N).unwrap();
    let s2_ntt = Polynomial::new(s2.iter().map(|a| Felt::new(*a)).collect_vec()).fft();
    let h_ntt = pk.h.fft();
    let c_ntt = c.fft();

    // s1 = c - s2 * pk.h;
    let s1_ntt = c_ntt - s2_ntt.hadamard_mul(&h_ntt);
    let s1 = s1_ntt.ifft();
    let s2 = s2_ntt.ifft();

    let public = FalconInput {
        h: (&pk.h).into(),
        c: (&c).into(),
    };

    let sig = FalconSig {
        s1: (&s1).into(),
        s2: (&s2).into(),
    };

    (public, sig)
}

#[derive(Clone, Debug)]
pub struct FalconPoly<const N: usize>([u16; N]);

impl<const N: usize> FalconPoly<N> {
    pub fn new() -> Self {
        Self([0u16; N])
    }

    pub fn from_coeffs(coeffs: [u16; N]) -> Self {
        Self(coeffs)
    }

    pub fn coeffs(&self) -> &[u16] {
        &self.0
    }

    pub fn coeffs_mut(&mut self) -> &mut [u16] {
        &mut self.0
    }
}

impl<const N: usize> Default for FalconPoly<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> FalconPoly<N> {
    /// Calculate the l2-norm (squared)
    pub fn norm_squared(&self) -> u64 {
        self.0
            .iter()
            .map(|c| {
                let m = if *c > FALCON_MOD / 2 {
                    FALCON_MOD - c
                } else {
                    *c
                };
                m as u64 * m as u64
            })
            .sum::<u64>()
    }
}

impl<const N: usize> From<&Polynomial<Felt>> for FalconPoly<N> {
    fn from(p: &Polynomial<Felt>) -> Self {
        Self(core::array::from_fn(|i| p.coefficients[i].value() as u16))
    }
}

impl<const N: usize> From<[u16; N]> for FalconPoly<N> {
    fn from(coeffs: [u16; N]) -> Self {
        Self::from_coeffs(coeffs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::Rng;
    use rand::thread_rng;

    #[test]
    fn test_falcon_512() {
        let msg = b"Hello, world!";
        let (sk, pk) = Falcon512::keygen(thread_rng().r#gen());
        let sig = Falcon512::sign(msg, &sk);
        assert!(Falcon512::verify(msg, &sig, &pk));
    }

    #[test]
    fn test_falcon_1024() {
        let mut rng = thread_rng();
        let msg: [u8; 5] = rng.r#gen();
        let (sk, pk) = Falcon1024::keygen(rng.r#gen());
        let sig = Falcon1024::sign(&msg, &sk);
        assert!(Falcon1024::verify(&msg, &sig, &pk));
    }
}
