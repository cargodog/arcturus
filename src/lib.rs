//! A light-weight and performant implementation of the Arcturus zero-knowledge proof system
//! [[link](https://eprint.iacr.org/2020/312)].

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
