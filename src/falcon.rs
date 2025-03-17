use falcon_rust::falcon512;
use falcon_rust::falcon1024;

use rand::thread_rng;
use rand::Rng;


mod tests {
    use super::*;

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
        let msg : [u8; 5] = rng.r#gen();
        let (sk, pk) = falcon1024::keygen(rng.r#gen());
        let sig = falcon1024::sign(&msg, &sk);
        assert!(falcon1024::verify(&msg, &sig, &pk));
    }
}




