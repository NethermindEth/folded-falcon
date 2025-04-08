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
    falcon_field::Felt,
    falcon512::{PublicKey, Signature},
    fast_fft::FastFft,
    polynomial::{Polynomial, hash_to_point}
};
use itertools::Itertools;

const N: usize = 512;

pub fn deserialize(m: &[u8], sig: &Signature, pk: &PublicKey) -> (FalconInput, FalconSig) {
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

    let p2v = |poly: &Polynomial<Felt>| -> Vec<u128> {
        poly.coefficients.iter().map(|c| c.value() as u128).collect_vec()
    };

    let public = FalconInput {
        h: p2v(&pk.h),
        c: p2v(&c),
    };

    let sig = FalconSig {
        s1: p2v(&s1),
        s2: p2v(&s2),
    };

    (public, sig)
}

#[cfg(test)]
mod tests {
    use falcon_rust::falcon512;
    use falcon_rust::falcon1024;

    use rand::Rng;
    use rand::thread_rng;

    #[test]
    fn test_falcon_512() {
        let msg = b"Hello, world!";
        let (sk, pk) = falcon512::keygen(thread_rng().r#gen());
        let sig = falcon512::sign(msg, &sk);
        assert!(falcon512::verify(msg, &sig, &pk));
    }

    #[test]
    fn test_falcon_1024() {
        let mut rng = thread_rng();
        let msg: [u8; 5] = rng.r#gen();
        let (sk, pk) = falcon1024::keygen(rng.r#gen());
        let sig = falcon1024::sign(&msg, &sk);
        assert!(falcon1024::verify(&msg, &sig, &pk));
    }
}
