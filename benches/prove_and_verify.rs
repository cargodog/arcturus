use arcturus::proof::*;
use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput, SamplingMode};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::rngs::OsRng; // You should use a more secure RNG
use std::iter;


fn setup_prover_data(n: usize, m: usize, w: usize) -> (ArcturusGens, Vec<Output>, Vec<usize>, Vec<SpendSecret>, Vec<MintSecret>) {
    let gens = ArcturusGens::new(n, m, w).unwrap();
    let ring_size = gens.ring_size();

    // Build a random ring of outputs
    let mut ring = iter::repeat_with(|| {
        Output::new(
            RistrettoPoint::random(&mut OsRng),
            RistrettoPoint::random(&mut OsRng),
        )
    })
    .take(ring_size)
    .collect::<Vec<_>>();

    // Generate the secret data for this proof
    let idxs = vec![3, 4, 7]; // Each proof spends 3 inputs and mints 3 outputs
    let mut spends = Vec::new();
    let mut mints = Vec::new();
    for &idx in &idxs {
        let privkey = Scalar::random(&mut OsRng);
        let pubkey = RistrettoPoint::random(&mut OsRng);
        let amount = 6600;
        let blind_spend = Scalar::random(&mut OsRng);
        let blind_mint = Scalar::random(&mut OsRng);
        let spend = SpendSecret::new(privkey, amount, blind_spend);
        let mint = MintSecret::new(pubkey, amount, blind_mint);
        ring[idx] = spend.to_output();
        spends.push(spend);
        mints.push(mint);
    }

    (gens, ring, idxs, spends, mints)
}

fn proof_time(c: &mut Criterion) {
    let mut group = c.benchmark_group("Proof Time");
    group.sample_size(10);

    // Iterate over list of proof configs (n, m, w)
    for cfg in [
        (16, 2, 3),
        (16, 3, 3),
        (16, 4, 3),
    ]
    .iter()
    {
        let (gens, ring, idxs, spends, mints) = setup_prover_data(cfg.0, cfg.1, cfg.2);
        group.throughput(Throughput::Elements(1));
        group.bench_with_input(
            BenchmarkId::from_parameter(gens.ring_size()),
            &(ring, idxs, spends, mints),
            |b, (ring, idxs, spends, mints)| {
                b.iter(|| {
                    gens.prove(
                        &mut Transcript::new(b"Arcturus-Becnhmark"),
                        &ring[..],
                        &idxs[..],
                        &spends[..],
                        &mints[..],
                    )
                    .unwrap()
                });
            },
        );
    }
    group.finish();
}

fn verification_time(c: &mut Criterion) {
    static BATCH_SIZE: usize = 1024;
    let mut group = c.benchmark_group("Verification Time");
    group.sample_size(10);

    // Iterate over list of proof configs (n, m, w)
    for cfg in [
        (16, 2, 3),
        (16, 3, 3),
        (16, 4, 3),
    ]
    .iter()
    {
        let (gens, ring, idxs, spends, mints) = setup_prover_data(cfg.0, cfg.1, cfg.2);
        let proof = gens.prove(
                &mut Transcript::new(b"Arcturus-Becnhmark"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .unwrap();
        let proofs = iter::once(proof).cycle().take(BATCH_SIZE).collect::<Vec<_>>();
        group.throughput(Throughput::Elements(BATCH_SIZE as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(gens.ring_size()),
            &(ring, idxs, spends, mints),
            |b, (ring, idxs, spends, mints)| {
                b.iter(|| {
                    gens.verify(
                        &mut Transcript::new(b"Arcturus-Becnhmark"),
                        &ring[..],
                        &proofs[..],
                    )
                    .unwrap()
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, verification_time);
criterion_main!(benches);
