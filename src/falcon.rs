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
