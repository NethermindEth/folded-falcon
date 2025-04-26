use criterion::{Criterion, criterion_group, criterion_main};
use std::time::Duration;

use folded_falcon::{
    LFAcc, LFComp, LFVerifier, SplitRing,
    falcon::{Falcon512, FalconOps, FalconParams},
    r1cs::{signature_verification_r1cs, signature_verification_splitring_z},
};

use anyhow::Result;
use cyclotomic_rings::rings::{FrogChallengeSet as CS, FrogRingNTT as RqNTT};
use latticefold::{
    arith::{Arith, CCCS, CCS, Witness},
    commitment::AjtaiCommitmentScheme,
    decomposition_parameters::DecompositionParams,
};
use rand::Rng;

type Falcon = Falcon512;
const K: usize = 32;
type SplitNTT = SplitRing<RqNTT, K>;

const C: usize = 38;
const W: usize = WIT_LEN * DP::L;
const WIT_LEN: usize = 3260 * 2;
type Ajtai = AjtaiCommitmentScheme<C, W, RqNTT>;

#[derive(Clone)]
pub struct DP {}
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
    let (x0, w0) = Falcon::deserialize(msg, &sig, &pk);

    let msg = b"Bye, world!";
    let (sk, pk) = Falcon::keygen(rand::thread_rng().r#gen());
    let sig = Falcon::sign(msg, &sk);
    let (x1, w1) = Falcon::deserialize(msg, &sig, &pk);

    let (r1cs, map) = signature_verification_r1cs::<SplitNTT>(2, Falcon::N, Falcon::LSB2);
    let z = signature_verification_splitring_z::<_, K, { Falcon::N }>(
        &[(x0, w0), (x1, w1)],
        Falcon::LSB2,
        map,
    )?;

    let x_len = r1cs.l;
    //println!("WIT_LEN: {}", z.len() - x_len - 1);
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

fn criterion_benchmark(c: &mut Criterion) {
    let mut rng = rand::thread_rng();

    let scheme = Ajtai::rand(&mut rng);
    let comp0 = dummy_comp(&scheme).unwrap();
    let (mut agg, proof) = LFAcc::<RqNTT, DP, CS, C, W>::init(scheme, &comp0).unwrap();

    // Prover / Fold
    let comp = dummy_comp(agg.ajtai()).unwrap();
    let mut agg0 = agg.clone();
    c.bench_function("fold2", |b| {
        b.iter(|| {
            agg.fold(&comp).unwrap();
        })
    });

    // Verifier
    let mut ctx = LFVerifier::<RqNTT, DP, CS, C>::init(&comp0, &proof).unwrap();
    c.bench_function("verify2", |b| {
        b.iter_batched(
            || (agg0.fold(&comp).unwrap(), comp.clone().into()),
            |(proof, compv)| ctx.verify(&compv, &proof).unwrap(),
            criterion::BatchSize::SmallInput,
        )
    });
}

criterion_group!(
    name=benches;
    config = Criterion::default().sample_size(10).measurement_time(Duration::from_secs(50)).warm_up_time(Duration::from_secs(1));
    targets = criterion_benchmark);
criterion_main!(benches);
