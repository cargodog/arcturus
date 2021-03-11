#![allow(non_snake_case)]
use crate::output::Output;
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "std")]
use std::vec::Vec;

/// Zero-knowledge proof that some minted outputs are valid spends of existing outputs in a ring
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Proof {
    pub(crate) mints: Vec<Output>,
    pub(crate) A: RistrettoPoint,
    pub(crate) B: RistrettoPoint,
    pub(crate) C: RistrettoPoint,
    pub(crate) D: RistrettoPoint,
    pub(crate) X_j: Vec<RistrettoPoint>,
    pub(crate) Y_j: Vec<RistrettoPoint>,
    pub(crate) Z_j: Vec<RistrettoPoint>,
    pub(crate) J_u: Vec<RistrettoPoint>,
    pub(crate) f_uji: Vec<Vec<Vec<Scalar>>>,
    pub(crate) zA: Scalar,
    pub(crate) zC: Scalar,
    pub(crate) zR_u: Vec<Scalar>,
    pub(crate) zS: Scalar,
}

impl Proof {
    pub fn count_spends(&self) -> usize {
        self.J_u.len()
    }

    pub fn count_mints(&self) -> usize {
        self.mints.len()
    }

    pub fn tags(&self) -> &Vec<RistrettoPoint> {
        &self.J_u
    }

    pub fn mints(&self) -> &Vec<Output> {
        &self.mints
    }
}
