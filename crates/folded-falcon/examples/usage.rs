//! Example demonstrating the basic usage of folded-falcon.
//!
//! This example shows how to:
//! 1. Create and initialize computations
//! 2. Fold/prove computations
//! 3. Verify folded proofs
//! 4. Serialize and deserialize proofs

use rand;

use folded_falcon::{
    LFAcc, LFComp, LFVerifier,
    config::{F512Frog16 as FR, FoldedRing},
    falcon::FalconOps,
};

use anyhow::Result;

use cyclotomic_rings::rings::{FrogChallengeSet as CS, FrogRingNTT as RqNTT};
use latticefold::{
    arith::{Arith, CCCS, CCS, Witness},
    commitment::AjtaiCommitmentScheme,
    decomposition_parameters::DecompositionParams,
};
use rand::Rng;

type Falcon = <FR as FoldedRing>::Variant;

const C: usize = 38;
const W: usize = WIT_LEN * DP::L;
const WIT_LEN: usize = 3260;
type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;

#[derive(Clone)]
struct DP {}
impl DecompositionParams for DP {
    const B: u128 = 131072;
    const L: usize = 4;
    const B_SMALL: usize = 2;
    const K: usize = 17;
}

fn dummy_comp(ajtai: &Ajtai) -> Result<LFComp<RqNTT, C>> {
    let msg = b"Hello, world!";
    let (sk, pk) = Falcon::keygen(rand::thread_rng().r#gen());
    let sig = Falcon::sign(msg, &sk);

    let (x, w) = Falcon::deserialize(msg, &sig, &pk);

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

    // Step 5: Initialize verifier
    let mut ctx = LFVerifier::<RqNTT, DP, CS, C>::init(&comp0, &proof)?;

    // Step 6: Verify the folded proof
    let compv = comp.clone().into();
    let result = ctx.verify(&compv, &fold_proof)?;
    println!("Verification result: {:?}", result);

    Ok(())
}
