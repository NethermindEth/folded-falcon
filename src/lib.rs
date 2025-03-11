mod lfold;

pub use lfold::{LFAcc, LFComp, LFVerifier};

/// Witness, signature vector components
#[derive(Clone, Debug)]
pub struct FalconSig {
    pub s1: Vec<u8>,
    pub s2: Vec<u8>,
}

/// Statement (public input)
#[derive(Clone, Debug)]
pub struct FalconInput {
    /// Message
    pub msg: Vec<u8>,
    /// Public key
    pub h: Vec<u8>,
    /// Salt
    pub r: Vec<u8>,
}
