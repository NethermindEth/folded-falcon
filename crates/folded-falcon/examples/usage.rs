//! Example demonstrating the basic usage of folded-falcon.
//!
//! This example shows how to:
//! 1. Create and initialize computations
//! 2. Fold/prove computations
//! 3. Verify folded proofs
//! 4. Serialize and deserialize proofs

use folded_falcon::{
    LFAcc, LFComp, LFVerifier,
    config::{F512Frog16 as FR, FoldedRing},
    falcon::FalconOps,
};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use anyhow::Result;
use latticefold::nifs::LFProof;
use std::io::Cursor;

use cyclotomic_rings::rings::{FrogChallengeSet as CS, FrogRingNTT as RqNTT};
use latticefold::{
    arith::{Arith, CCCS, CCS, Witness},
    commitment::AjtaiCommitmentScheme,
    decomposition_parameters::DecompositionParams,
};
use rand::Rng;

type Falcon = <FR as FoldedRing>::Variant;

// Security parameter for Ajtai commitments (length of Ajtai commitment vectors).
const C: usize = 38;
// Effective witness length after decomposition (original witness length * number of limbs).
const W: usize = WIT_LEN * DP::L;
// Original witness length before decomposition.
const WIT_LEN: usize = 3260;
type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;

// Struct to hold decomposition parameters.
#[derive(Clone)]
struct DP {}
// Implementation of decomposition parameters for the DP struct.
impl DecompositionParams for DP {
    // Large modulus or bound for decomposition.
    const B: u128 = 131072;
    // Number of levels or limbs in the decomposition.
    const L: usize = 4;
    // Smaller base or bound used in decomposition.
    const B_SMALL: usize = 2;
    // Parameter K for decomposition (e.g., bits per limb or security parameter).
    const K: usize = 17;
}

fn dummy_comp(ajtai: &Ajtai) -> Result<LFComp<RqNTT, C>> {
    let msg = b"Hello, world!";
    let (sk, pk) = Falcon::keygen(rand::thread_rng().r#gen());
    let sig = Falcon::sign(msg, &sk);

    let (x, w) = Falcon::deserialize(msg, &sig, &pk);

    // The number 1 for the FR::r1cs(1) function represents the number of signature verifications per circuit.
    let (r1cs, map) = FR::r1cs(1);
    let z = FR::z(&[(x, w)], map).unwrap();

    let x_len = r1cs.l;
    r1cs.check_relation(&z)?;

    let ccs = CCS::from_r1cs_padded(r1cs, W, DP::L);
    ccs.check_relation(&z)?;

    let wit: Witness<RqNTT> = Witness::from_w_ccs::<DP>(z[x_len + 1..].to_vec());
    let cm_i = CCCS {
        cm: wit.commit::<C, W, DP>(ajtai)?,
        x_ccs: z[..x_len].to_vec(),
    };

    Ok(LFComp {
        witness: wit,
        cccs: cm_i,
        ccs,
    })
}

fn main() -> Result<()> {
    // Step 1: Initialize Ajtai scheme and create computation
    let mut rng = rand::thread_rng();
    let scheme = Ajtai::rand(&mut rng);
    let comp0 = dummy_comp(&scheme)?;

    // Step 2: Initialize accumulator and get initial proof
    let (mut acc, proof) = LFAcc::<RqNTT, DP, CS, C, W>::init(scheme, &comp0)?;

    // Step 3: Create another computation
    let comp = dummy_comp(acc.ajtai())?;

    // Step 4: Fold computation into accumulator
    let fold_proof = acc.fold(&comp)?;

    // Step 4.1: Serialize the proof
    let mut serialized_proof = Vec::new();
    fold_proof.serialize_compressed(&mut serialized_proof)?;
    println!("Serialized proof size: {} bytes", serialized_proof.len());

    // Step 4.2: Deserialize the proof
    let mut cursor = Cursor::new(&serialized_proof[..]);
    let deserialized_proof = LFProof::<C, RqNTT>::deserialize_compressed(&mut cursor)?;
    println!(
        "Deserialized proof size: {:?} bytes",
        deserialized_proof.compressed_size()
    );

    // Step 5: Initialize verifier
    let mut ctx = LFVerifier::<RqNTT, DP, CS, C>::init(&comp0, &proof)?;

    // Step 6: Verify the folded proof
    let compv = comp.clone().into();
    ctx.verify(&compv, &fold_proof)?;
    println!("Verification result: {:?}", ("Verification OK".to_string()));

    Ok(())
}
