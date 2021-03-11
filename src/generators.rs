#![allow(non_snake_case)]
use crate::errors::{ArcturusError, ArcturusResult};
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use blake2::Blake2b;
use curve25519_dalek::constants;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "std")]
use std::vec::Vec;

/// Generator points to be used in proof computations
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Generators {
    pub(crate) n: usize,
    pub(crate) m: usize,
    pub(crate) w: usize,
    pub(crate) G: RistrettoPoint,
    pub(crate) U: RistrettoPoint,
    pub(crate) H_uji: Vec<Vec<Vec<RistrettoPoint>>>,
}

impl Generators {
    /// Compute a new set of generators.
    ///
    /// This will precompute the generators necessary an `m` digit `n`-ary anonymity set. For
    /// example, if `n = 2`, `m = 8`, the computed generators will support proofs with an anonymity
    /// set of `2^8 = 256`.
    ///
    /// This will also precompute generators for up to `w` signers in a proof.
    pub fn new(n: usize, m: usize, w: usize) -> ArcturusResult<Generators> {
        if n < 2 || m < 2 || w < 1 {
            return Err(ArcturusError::BadArg);
        }
        if let Some(x) = n.checked_pow(m as u32) {
            if w > x {
                return Err(ArcturusError::InvalidDimensions);
            }
        } else {
            return Err(ArcturusError::Overflow);
        }

        // G is the Ristretto basepoint.
        // U is derived from hash(G) directly.
        // Each of H[u][j][i] are computed as an indexed derivation from G.
        let G = constants::RISTRETTO_BASEPOINT_POINT;
        let U = RistrettoPoint::hash_from_bytes::<Blake2b>(G.compress().as_bytes());
        let mut H_uji = Vec::new();
        for u in 0..w {
            H_uji.push(Vec::new());
            for j in 0..m {
                H_uji[u].push(Vec::new());
                for i in 0..n {
                    H_uji[u][j].push(derive_generator(&G, u as u32, j as u32, i as u32));
                }
            }
        }

        Ok(Generators {
            n,
            m,
            w,
            G,
            U,
            H_uji,
        })
    }

    /// Returns the ring size required for proof/verification.
    pub fn ring_size(&self) -> usize {
        self.n.checked_pow(self.m as u32).unwrap()
    }

    /// Create a Pedersen commitment, with value `v` and blinding factor `r`.
    pub fn commit(&self, v: &Scalar, r: &Scalar) -> RistrettoPoint {
        v * self.H_uji[0][0][0] + r * self.G
    }
}

/// Derive a generator point from some other base point, without a known logarithm.
/// A generator is derived by hashing 3 derivation indices (u, j, i) and the base point.
///
/// For example, to derive a new generator H_123 from base point G:
/// H_123 = hash(1 || 2 || 3 || G)
pub(crate) fn derive_generator(base: &RistrettoPoint, u: u32, j: u32, i: u32) -> RistrettoPoint {
    let mut bytes = [0u8; 4 + 4 + 4 + 32];
    bytes[0..4].copy_from_slice(&u.to_be_bytes());
    bytes[4..8].copy_from_slice(&j.to_be_bytes());
    bytes[8..12].copy_from_slice(&i.to_be_bytes());
    bytes[12..].copy_from_slice(base.compress().as_bytes());
    RistrettoPoint::hash_from_bytes::<Blake2b>(&bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::ristretto::CompressedRistretto;

    const G: RistrettoPoint = constants::RISTRETTO_BASEPOINT_POINT;
    const H: CompressedRistretto = CompressedRistretto([
        88, 20, 136, 75, 248, 210, 190, 177, 173, 233, 152, 155, 220, 94, 58, 58, 119, 94, 58, 212,
        93, 51, 131, 1, 105, 167, 53, 130, 234, 250, 194, 116,
    ]);

    #[test]
    fn test_new() {
        let gens = Generators::new(3, 2, 1).unwrap();
        assert_eq!(gens.H_uji[0][0].len(), 3);
        assert_eq!(gens.H_uji[0].len(), 2);
        assert_eq!(gens.H_uji.len(), 1);
        assert!(Generators::new(1, 3, 3).is_err());
        assert!(Generators::new(2, 3, 3).is_ok());
        assert!(Generators::new(32, 3, 3).is_ok());
        assert!(Generators::new(3, 1, 3).is_err());
        assert!(Generators::new(3, 2, 3).is_ok());
        assert!(Generators::new(2, 32, 3).is_ok());
        assert!(Generators::new(3, 3, 0).is_err());
        assert!(Generators::new(3, 3, 1).is_ok());
        assert!(Generators::new(2, 6, 32).is_ok());
        assert!(Generators::new(2, 6, 33).is_ok());
        assert!(Generators::new(3, 3, 27).is_ok());
        assert!(Generators::new(3, 3, 28).is_err());
    }

    #[test]
    fn test_commit() {
        let gens = Generators::new(2, 2, 1).unwrap();
        let A = gens.commit(&Scalar::from(100u32), &Scalar::from(10u32));
        let B = gens.commit(&Scalar::from(200u32), &Scalar::from(20u32));
        let C = gens.commit(&Scalar::from(300u32), &Scalar::from(30u32));
        assert_eq!(
            A,
            Scalar::from(100u32) * H.decompress().unwrap() + Scalar::from(10u32) * G
        );
        assert_eq!(
            B,
            Scalar::from(200u32) * H.decompress().unwrap() + Scalar::from(20u32) * G
        );
        assert_eq!(
            C,
            Scalar::from(300u32) * H.decompress().unwrap() + Scalar::from(30u32) * G
        );
        assert_eq!(A + B, C);
    }

    struct DeriveGeneratorTest {
        u: u32,
        j: u32,
        i: u32,
        generator: CompressedRistretto,
    }
    const DERIVE_GENERATOR_TESTS: [DeriveGeneratorTest; 6] = [
        DeriveGeneratorTest {
            u: 0,
            j: 0,
            i: 0,
            generator: CompressedRistretto([
                88, 20, 136, 75, 248, 210, 190, 177, 173, 233, 152, 155, 220, 94, 58, 58, 119, 94,
                58, 212, 93, 51, 131, 1, 105, 167, 53, 130, 234, 250, 194, 116,
            ]),
        },
        DeriveGeneratorTest {
            u: 1,
            j: 0,
            i: 0,
            generator: CompressedRistretto([
                194, 178, 89, 2, 84, 132, 230, 112, 111, 226, 126, 224, 100, 225, 99, 113, 234,
                154, 248, 153, 151, 20, 241, 215, 167, 41, 143, 186, 226, 102, 24, 102,
            ]),
        },
        DeriveGeneratorTest {
            u: 4,
            j: 2,
            i: 0,
            generator: CompressedRistretto([
                190, 51, 77, 158, 51, 108, 81, 214, 169, 221, 29, 236, 210, 81, 120, 253, 195, 129,
                138, 218, 234, 193, 31, 250, 63, 255, 164, 71, 60, 86, 17, 39,
            ]),
        },
        DeriveGeneratorTest {
            u: 0,
            j: 7,
            i: 0,
            generator: CompressedRistretto([
                44, 116, 102, 244, 143, 42, 93, 185, 204, 252, 252, 110, 196, 102, 171, 18, 65, 49,
                74, 10, 47, 179, 33, 117, 24, 201, 186, 113, 3, 199, 231, 113,
            ]),
        },
        DeriveGeneratorTest {
            u: 0,
            j: 99,
            i: 1,
            generator: CompressedRistretto([
                182, 55, 187, 58, 199, 199, 90, 204, 88, 82, 218, 223, 188, 38, 201, 224, 102, 78,
                0, 120, 209, 78, 145, 12, 131, 99, 122, 39, 48, 105, 115, 10,
            ]),
        },
        DeriveGeneratorTest {
            u: 0,
            j: 0,
            i: 8,
            generator: CompressedRistretto([
                30, 100, 155, 211, 42, 105, 108, 57, 11, 133, 58, 177, 173, 137, 199, 29, 138, 170,
                187, 139, 115, 155, 94, 70, 186, 98, 54, 104, 72, 213, 139, 108,
            ]),
        },
    ];

    #[test]
    fn test_derive_generator() {
        for test in &DERIVE_GENERATOR_TESTS {
            assert_eq!(
                &test.generator,
                &derive_generator(&G, test.u, test.j, test.i).compress()
            );
        }
    }
}
