//! A light-weight and performant implementation of the Arcturus zero-knowledge proof system
//! [[link](https://eprint.iacr.org/2020/312)].

#![cfg_attr(not(feature = "std"), no_std)]

//-----------------------------------------------------------------------------
// External dependencies:
//-----------------------------------------------------------------------------
#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;
extern crate blake2;
extern crate curve25519_dalek;
extern crate itertools;
extern crate polynomials;

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
#[macro_use]
pub(crate) mod util;
