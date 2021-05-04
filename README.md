# ⚠️  Security Warning
A break has been identified in the security assumptions as written in the Arcutur paper. This project exists for research purposes and historical context only, and under no circumstances should be used in any real application. Read more about the break here: https://github.com/cargodog/arcturus/issues/43


# arcturus
A pure Rust, light-weight, and performant implementation of the Arcturus zero-knowledge
proof system [[link][arcturus-paper]].

Arcturus enables efficient proof and verification of confidential transactions with very large
anonymity sets. A correct proof provides the following guarantees:
1) The signer posesses the signing key for each spent output in the ring.
1) The sum of spent inputs matches the sum of newly minted outputs.<sup>[1](#usage-notes)</sup>
1) Each spent input is accompanied with a unique, deterministic, linking tag to detect double
   spends.<sup>[2](#usage-notes)</sup>
1) The transaction input and output values are hidden (aka confidential).
1) The transaction inputs and signing keys are hidden in a large anonymity set.<sup>[3](#usage-notes)</sup>

# Documentation
Detailed documentation can be found [here][docs-external].

# Usage and Features
Latest release version can be found in the git tags or on [crates.io][arcturus-crate]. Add the latest version to your project's `Cargo.toml`:
```toml
arcturus = "x.y.z"
```

By default, `std` and `serde` features are enabled. To build without `std` or without `serde`
implementations, use the `--no-default-features` option when building. Note, if default features
are disabled, a backend must be specified. The available backends are:
* `simd_backend`
* `u64_backend`
* `u32_backend`

The following example
builds without `std`, but still implements `serde`:
```sh
cargo build --no-default-features --features "serde simd_backend"
```

Please keep the following points in mind when building a project around this library:
1) This library does not include range proofs. To ensure no input or output value is
negative, each input and output commitment should be accompanied with a range proof, such as
[bulletproofs][bulletproofs-crate]. Failure to prevent negative inputs or outputs
could allow an attacker to create new coins (e.g. inflation bug).

2) To prevent double spends, each input's linking tag should be checked for uniqueness and
recorded in a list of spent outputs. If a tag is ever seen twice, this means that the
corresponding input has already been spent.

3) This library leaves selection of the anonymity set up to the user. Selecting a good
ring of UTXOs is essential to providing anonymity for the signer and his transaction inputs.


# Example:
```rust
use arcturus::*;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::rngs::OsRng; // You should use a more secure RNG

// Set up proof generators for 5 bit binary proofs with up to 2 spends in a proof.
let gens = ArcturusGens::new(2, 5, 2).unwrap();

// Given a ring of UTXOs, assume the signer controls outputs at indices 13 & 14 (signer knows spend
// key, amount, and blinding factor for each of his inputs) and wishes to spend those inputs in a
// transaction which mints a new output whose value balances against the inputs:
let ring: Vec<Arcturus::Output> = ...;

// Indices of UTXOs to spend as transaction inputs
let idxs = vec![13, 14];

// Secret data to spend each input UTXO
let spends = vec![ // Secret data to spend each input UTXO
    SpendSecret::new(spend_key_13, spend_amt_13, spend_blind_13),
    SpendSecret::new(spend_key_14, spend_amt_14, spend_blind_14)
];

// Secret data for new minted outputs (Total mint ammounts must balance total input ammounts).
let mints = vec![MintSecret::new(mint_pubkey, mint_amt, mint_blind)];

// Signer computes the transaction proof
let mut t = Transcript::new(b"Test proof");
let proof = gens.prove(&mut t, &ring[..], &idxs[..], &spends[..], &mints[..]).unwrap();

// The verifier my verify the proof as follows:
let mut t = Transcript::new(b"Test proof");
let proofs = vec![proof];
assert!(gens.verify(&mut t, &ring[..], &proofs[..]).is_ok());
```

# Performance
Benchmarks are run using [criterion.rs][criterion-crate].
```sh
export RUSTFLAGS="-C target_cpu=native"
cargo bench --no-default-features --features "std simd_backend serde"
```

# Contributing
Please see [CONTRIBUTING.md][contributing].


[arcturus-paper]: https://eprint.iacr.org/2020/312
[arcturus-crate]: https://crates.io/crates/arcturus
[docs-external]: https://docs.rs/arcturus
[bulletproofs-crate]: https://crates.io/crates/bulletproofs
[criterion-crate]: https://crates.io/crates/criterion
[contributing]: https://github.com/cargodog/arcturus/blob/master/CONTRIBUTING.md
