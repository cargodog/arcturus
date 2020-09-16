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

## ⚠️  Security Warning
This crate is a work in progress and has not been independently audited!

USE AT YOUR OWN RISK!

## Documentation
Detailed documentation can be found [here][docs-external].

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
cargo bench
```

# Contributing
Please see [CONTRIBUTING.md][contributing].

# Usage notes
1) This library does not include range proofs. To ensure no input or output value is
negative, each input and output commitment should be accompanied with a range proof, such as
[bulletproofs][bulletproofs-crate]. Failure to prevent negative inputs or outputs
could allow an attacker to create new coins (e.g. inflation bug).

2) To prevent double spends, each input's linking tag should be checke for uniqueness and
recorded in a list of spent outputs. If a tag is ever seen twice, this means that the
corresponding input has already been spent.

3) This library leaves selection of the anonymity set up to the user. Selecting a good
ring of UTXOs is essential to providing anonymity for the signer and his transaction inputs.


[arcturus-paper]: https://eprint.iacr.org/2020/312
[docs-external]: https://docs.rs/arcturus
[bulletproofs-crate]: https://crates.io/crates/bulletproofs
[criterion-crate]: https://crates.io/crates/criterion
[contributing]: https://github.com/cargodog/arcturus/blob/master/CONTRIBUTING.md
