//! A light-weight and performant implementation of the Arcturus zero-knowledge proof system
//! [[link](https://eprint.iacr.org/2020/312)].
//!
//! Arcturus enables efficient proof and verification of confidential transactions with very large
//! anonymity sets. A correct proof provides the following guarantees:
//! 1) The signer posesses the signing key for each spent output in the ring.
//! 1) The sum of spent inputs matches the sum of newly minted outputs.<sup>1</sup>
//! 1) Each spent input is accompanied with a unique, deterministic, linking tag to detect double
//!    spends.<sup>2</sup>
//! 1) The transaction input and output values are hidden (aka confidential).
//! 1) The transaction inputs and signing keys are hidden in a large anonymity set.<sup>3</sup>
//!
//! # Example:
//! ```
//! use arcturus::*;
//! use curve25519_dalek::ristretto::RistrettoPoint;
//! use curve25519_dalek::scalar::Scalar;
//! use merlin::Transcript;
//! use rand::rngs::OsRng; // You should use a more secure RNG
//! # use std::iter;
//!
//! // Set up proof generators for 5 bit binary proofs with up to 2 spends in a proof.
//! let gens = ArcturusGens::new(2, 5, 2).unwrap();
//!
//! // Given a ring of UTXOs, assume the signer controls outputs at indices 13 & 14, with the
//! // following spend keys, amounts, and blinding factors:
//! let spend_key_13 = Scalar::random(&mut OsRng);
//! let spend_amt_13 = 100;
//! let spend_blind_13 = Scalar::random(&mut OsRng);
//! let spend_key_14 = Scalar::random(&mut OsRng);
//! let spend_amt_14 = 200;
//! let spend_blind_14 = Scalar::random(&mut OsRng);
//!
//! // Assume the spender wishes to mint the following output, which balance against the spent
//! // inputs:
//! let mint_pubkey = RistrettoPoint::random(&mut OsRng);
//! let mint_amt = 300;
//! let mint_blind = Scalar::random(&mut OsRng);
//!
//! // Compute the spend proof as follows:
//! let idxs = vec![13, 14];
//! let spends = vec![
//!     SpendSecret::new(spend_key_13, spend_amt_13, spend_blind_13),
//!     SpendSecret::new(spend_key_14, spend_amt_14, spend_blind_14)
//! ];
//! let mints = vec![MintSecret::new(mint_pubkey, mint_amt, mint_blind)];
//! # let mut ring = iter::repeat_with(|| {
//! #       Output::new(RistrettoPoint::random(&mut OsRng), RistrettoPoint::random(&mut OsRng))
//! #   })
//! #   .take(gens.ring_size())
//! #   .collect::<Vec<_>>();
//! # ring[13] = spends[0].to_output();
//! # ring[14] = spends[1].to_output();
//! #
//! let mut t = Transcript::new(b"Test proof");
//! let proof = gens.prove(&mut t, &ring[..], &idxs[..], &spends[..], &mints[..]).unwrap();
//!
//! // The verifier my verify the proof as follows:
//! let mut t = Transcript::new(b"Test proof");
//! let proofs = vec![proof];
//! assert!(gens.verify(&mut t, &ring[..], &proofs[..]).is_ok());
//! ```
//!
//! # Performance
//! Benchmarks are run using [criterion.rs](https://github.com/japaric/criterion.rs):
//! ```
//! export RUSTFLAGS="-C target_cpu=native"
//! cargo bench
//! ```
//!
//! *Note 1: This library does not include range proofs. To ensure no input or output value is
//! negative, each input and output commitment should be accompanied with a range proof, such as
//! [bulletproofs](https://docs.rs/bulletproofs). Failure to prevent negative inputs or outputs
//! could allow an attacker to create new coins (e.g. inflation bug).*
//!
//! *Note 2: To prevent double spends, each input's linking tag should be checke for uniqueness and
//! recorded in a list of spent outputs. If a tag is ever seen twice, this means that the
//! corresponding input has already been spent.*
//!
//! *Note 3: This library leaves selection of the anonymity set up to the user. Selecting a good
//! ring of UTXOs is essential to providing anonymity for the signer and his transaction inputs.*

#![no_std]
#![feature(test)]

//-----------------------------------------------------------------------------
// External dependencies:
//-----------------------------------------------------------------------------
extern crate blake2;
extern crate curve25519_dalek;
extern crate polynomials;

#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;

#[cfg(feature = "std")]
#[macro_use]
extern crate std;

//-----------------------------------------------------------------------------
// Public modules
//-----------------------------------------------------------------------------
pub mod errors;
pub mod proof;

//-----------------------------------------------------------------------------
// Re-exports
//-----------------------------------------------------------------------------
pub use proof::*;

//-----------------------------------------------------------------------------
// Internal modules
//-----------------------------------------------------------------------------
pub(crate) mod transcript;
pub(crate) mod util;
