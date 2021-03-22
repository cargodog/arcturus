#![allow(non_snake_case)]
use crate::errors::{ArcturusError, ArcturusResult};
use crate::generators::Generators;
use crate::output::{MintSecret, Output, SpendSecret};
use crate::proof::Proof;
use crate::transcript::TranscriptProtocol;
use crate::util::{exp_iter, sized_flatten, RadixDecomposer};
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::iter::{once, Iterator};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::MultiscalarMul;
use itertools::izip;
use merlin::Transcript;
use polynomials::Polynomial;
use rand::thread_rng;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "std")]
use std::vec::Vec;

macro_rules! flatten_2d {
    ( $ii:expr ) => {
        sized_flatten($ii.into_iter().map(|v| v.iter()))
    };
}

macro_rules! flatten_3d {
    ( $ii:expr ) => {
        sized_flatten(flatten_2d!($ii).into_iter().map(|v| v.iter()))
    };
}

/// Prover context
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Prover {
    gens: Generators,
    spends: Vec<SpendSecret>,
    mints: Vec<MintSecret>,
}

/// Prover context to build Arcturus proofs
impl Prover {
    pub fn new(n: usize, m: usize, w: usize) -> ArcturusResult<Prover> {
        let gens = Generators::new(n, m, w)?;
        let spends = Vec::new();
        let mints = Vec::new();
        Ok(Prover {
            gens,
            spends,
            mints,
        })
    }

    /// Returns the ring size required for proof/verification.
    pub fn ring_size(&self) -> usize {
        self.gens.ring_size()
    }

    pub fn push_spend(&mut self, spend_secret: SpendSecret) {
        self.spends.push(spend_secret);
    }

    pub fn pop_spend(&mut self) -> Option<SpendSecret> {
        self.spends.pop()
    }

    pub fn push_mint(&mut self, mint_secret: MintSecret) {
        self.mints.push(mint_secret);
    }

    pub fn pop_mint(&mut self) -> Option<MintSecret> {
        self.mints.pop()
    }

    /// Prove that newly minted outputs correctly spend existing outputs within the ring.
    ///
    /// > Note: this does not prove that an output has not been previously spent in a ledger. Each
    /// spent output yields a unique 'spend tag'. To avoid double spends, the verifier should query
    /// this proof for all spend tags, and confirm no spend tag has been used in a previous
    /// transaction.
    pub fn prove(&self, tscp: &mut Transcript, ring: &[Output]) -> ArcturusResult<Proof> {
        let n = self.gens.n;
        let m = self.gens.m;
        let w = self.spends.len();
        tscp.arcturus_domain_sep(n as u64, m as u64);

        if ring.len() != self.gens.ring_size() {
            return Err(ArcturusError::InvalidDimensions);
        }
        if w > self.gens.w {
            return Err(ArcturusError::TooManySpends);
        }

        // First make sure the mints and spends balance to zero
        if self.spends.iter().map(|s| s.amount).sum::<Scalar>()
            != self.mints.iter().map(|m| m.amount).sum::<Scalar>()
        {
            return Err(ArcturusError::MintsAndSpendsImbalance);
        }

        // Get the index of each spend within the ring
        let mut idxs = Vec::with_capacity(w);
        for s in self.spends.iter() {
            if let Some(idx) = ring.iter().position(|x| &s.output() == x) {
                idxs.push(idx);
            } else {
                return Err(ArcturusError::SpendNotFoundInRing);
            }
        }

        // Create a `TranscriptRng` from the high-level witness data
        //
        // The prover wants to rekey the RNG with its witness data (`l`and `r`).
        let mut rng = {
            let mut builder = tscp.build_rng();
            for &l in idxs.iter() {
                builder =
                    builder.rekey_with_witness_bytes(b"idx", Scalar::from(l as u32).as_bytes());
            }
            for s in self.spends.iter() {
                builder = builder.rekey_with_witness_bytes(b"privkey", s.privkey.as_bytes());
                builder = builder.rekey_with_witness_bytes(b"amount", s.amount.as_bytes());
                builder = builder.rekey_with_witness_bytes(b"blind", s.blind.as_bytes());
            }
            for m in &self.mints {
                builder = builder.rekey_with_witness_bytes(b"amount", m.amount.as_bytes());
                builder = builder.rekey_with_witness_bytes(b"blind", m.blind.as_bytes());
            }
            builder.finalize(&mut thread_rng())
        };

        let mut a_uji = (0..w)
            .map(|_| {
                (0..m)
                    .map(|_| (1..n).map(|_| Scalar::random(&mut rng)).collect())
                    .collect()
            })
            .collect::<Vec<Vec<Vec<_>>>>();
        for a_ji in a_uji.iter_mut() {
            for a_i in a_ji.iter_mut() {
                a_i.insert(0, -a_i.iter().sum::<Scalar>());
            }
        }

        // A = Com(a, rA) = rA*G + a_uji*H_uji
        let rA = Scalar::random(&mut rng);
        let A = RistrettoPoint::multiscalar_mul(
            once(&rA).chain(flatten_3d!(&a_uji[0..w])),
            once(&self.gens.G).chain(flatten_3d!(&self.gens.H_uji[0..w])),
        );

        // Convert each index from binary to a `m` digit `n-ary` number
        let sigma_uji = idxs
            .iter()
            .map(|&l| {
                RadixDecomposer::new(l, n)
                    .take(m)
                    .map(|l_j| {
                        let mut l_ji = vec![Scalar::zero(); n - 1];
                        l_ji.insert(l_j, Scalar::one());
                        l_ji
                    })
                    .collect()
            })
            .collect::<Vec<Vec<Vec<_>>>>();

        // B = Com(sigma, rB) = rB*G + sigma_uji*H_uji
        let rB = Scalar::random(&mut rng);
        let B = RistrettoPoint::multiscalar_mul(
            once(&rB).chain(flatten_3d!(&sigma_uji[0..w])),
            once(&self.gens.G).chain(flatten_3d!(&self.gens.H_uji[0..w])),
        );

        // C = Com(a*(1-2*sigma), rC) = rB*G + (a_uji*(1-2*sigma_uji))*H_uji
        let C_vals_uji = izip!(flatten_3d!(&sigma_uji[0..w]), flatten_3d!(&a_uji[0..w]))
            .map(|(sigma, a)| a * (Scalar::one() - Scalar::from(2u32) * sigma));
        let rC = Scalar::random(&mut rng);
        let C = RistrettoPoint::multiscalar_mul(
            once(rC).chain(C_vals_uji),
            once(&self.gens.G).chain(flatten_3d!(&self.gens.H_uji[0..w])),
        );

        // D = Com(-a^2, rD) = rD*G + -a_uji*a_uji*H_uji
        let rD = Scalar::random(&mut rng);
        let D = RistrettoPoint::multiscalar_mul(
            once(rD).chain(flatten_3d!(&a_uji[0..w]).map(|a| -a * a)),
            once(&self.gens.G).chain(flatten_3d!(&self.gens.H_uji[0..w])),
        );

        // Generate randomness rho & rhobar
        let rho_uj = (0..w)
            .map(|_| (0..m).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();
        let rhobar_uj = (0..w)
            .map(|_| (0..m).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();

        // Compute spend tags
        let J_u = self.spends.iter().map(|s| s.tag()).collect::<Vec<_>>();

        // Compute minted outputs
        let mints_pub = self.mints.iter().map(|m| m.output()).collect::<Vec<_>>();

        // Commit to public parameters so far
        for O in &mints_pub {
            tscp.append_point(b"pubkey", &O.pubkey.compress());
            tscp.append_point(b"commit", &O.commit.compress());
        }
        tscp.append_point(b"A", &A.compress());
        tscp.append_point(b"B", &B.compress());
        tscp.append_point(b"C", &C.compress());
        tscp.append_point(b"D", &D.compress());
        for J in &J_u {
            tscp.append_point(b"J", &J.compress());
        }

        let mut mu_k = exp_iter(tscp.challenge_scalar(b"mu"));
        mu_k.next(); // Skip mu^0

        // Build X_j, Y_j, & Z_j
        let (mut X_j, y_j, mut Z_j) =
            izip!(ring.iter().map(|O| (O.pubkey, O.commit)), mu_k.clone())
                .enumerate()
                .map(|(k, ((M, P), mu))| {
                    let p_j = idxs
                        .iter()
                        .enumerate()
                        .map(|(u, &l)| compute_p_j(k, l, &a_uji[u]))
                        .fold(vec![Scalar::zero(); m], |mut p_j, p_j_uth| {
                            for j in 0..m {
                                p_j[j] += p_j_uth[j];
                            }
                            p_j
                        });
                    let X_j_kth = p_j.iter().map(|p| p * mu * M).collect::<Vec<_>>();
                    let y_j_kth = p_j.iter().map(|p| p * mu).collect::<Vec<_>>();
                    let Z_j_kth = p_j.iter().map(|p| p * P).collect::<Vec<_>>();
                    (X_j_kth, y_j_kth, Z_j_kth)
                })
                .fold(
                    (
                        vec![RistrettoPoint::default(); m],
                        vec![Scalar::zero(); m],
                        vec![RistrettoPoint::default(); m],
                    ),
                    |(mut X_j, mut y_j, mut Z_j), (X_j_kth, y_j_kth, Z_j_kth)| {
                        for j in 0..m {
                            X_j[j] += X_j_kth[j];
                            y_j[j] += y_j_kth[j];
                            Z_j[j] += Z_j_kth[j];
                        }
                        (X_j, y_j, Z_j)
                    },
                );
        let mut Y_j = y_j.iter().map(|y| y * self.gens.U).collect::<Vec<_>>();
        for j in 0..m {
            X_j[j] += rho_uj.iter().map(|rho_j| rho_j[j]).sum::<Scalar>() * self.gens.G;
            Y_j[j] += izip!(&rho_uj, &J_u)
                .map(|(rho_j, J)| rho_j[j] * J)
                .sum::<RistrettoPoint>();
            Z_j[j] += rhobar_uj.iter().map(|rhobar_j| rhobar_j[j]).sum::<Scalar>() * self.gens.G;
        }

        // Commit to remaining public parameters
        for j in 0..m {
            tscp.append_point(b"X", &X_j[j].compress());
        }
        for j in 0..m {
            tscp.append_point(b"Y", &Y_j[j].compress());
        }
        for j in 0..m {
            tscp.append_point(b"Z", &Z_j[j].compress());
        }
        let x = tscp.challenge_scalar(b"x");
        let x_exp_m = exp_iter(x).nth(m).unwrap();

        let zA = rA + x * rB;
        let zC = rD + x * rC;
        let f_uji = izip!(sigma_uji, &a_uji)
            .map(|(sigma_ji, a_ji)| {
                izip!(sigma_ji, a_ji)
                    .map(|(sigma_i, a_i)| {
                        izip!(&sigma_i[1..], &a_i[1..])
                            .map(|(sigma, a)| sigma * x + a)
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let zR_u = izip!(idxs, self.spends.iter().map(|s| s.privkey), &rho_uj)
            .map(|(l, r, rho_j)| {
                mu_k.clone().nth(l).unwrap() * r * x_exp_m
                    - izip!(exp_iter(x), rho_j)
                        .map(|(exp_x, rho)| rho * exp_x)
                        .sum::<Scalar>()
            })
            .collect::<Vec<_>>();
        let zS = x_exp_m
            * (self.spends.iter().map(|s| s.blind).sum::<Scalar>()
                - self.mints.iter().map(|m| m.blind).sum::<Scalar>())
            - exp_iter(x)
                .take(m)
                .enumerate()
                .map(|(j, x_exp_j)| {
                    x_exp_j * rhobar_uj.iter().map(|rhobar_j| rhobar_j[j]).sum::<Scalar>()
                })
                .sum::<Scalar>();

        Ok(Proof {
            mints: mints_pub,
            A,
            B,
            C,
            D,
            X_j,
            Y_j,
            Z_j,
            J_u,
            f_uji,
            zA,
            zC,
            zR_u,
            zS,
        })
    }
}

fn compute_p_j(k: usize, l: usize, a_ji: &Vec<Vec<Scalar>>) -> Vec<Scalar> {
    let m = a_ji.len();
    let n = a_ji[0].len();

    // Create polynomials for each n
    let mut p = Polynomial::from(Vec::with_capacity(m));
    p.push(Scalar::one());

    // Convert k & l to vectors of n-ary digits
    let k = RadixDecomposer::new(k, n).take(m).collect::<Vec<_>>();
    let l = RadixDecomposer::new(l, n).take(m).collect::<Vec<_>>();

    // Multiply each polynomial
    for j in 0..m {
        let mut f = Polynomial::from(Vec::with_capacity(m));
        f.push(a_ji[j][k[j]]);
        if k[j] == l[j] {
            f.push(Scalar::one());
        }
        p *= f;
    }

    // Resize the vectors to be `m` bits wide
    let mut v: Vec<_> = p.into();
    v.resize_with(m, || Scalar::zero());
    v
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verifier::*;
    use rand::rngs::OsRng; // You should use a more secure RNG

    #[test]
    fn prove_2x5() {
        let mut prover = Prover::new(2, 5, 8).unwrap();

        // Build a random ring of outputs
        let mut ring = (0..prover.ring_size())
            .map(|_| {
                Output::new(
                    RistrettoPoint::random(&mut OsRng),
                    RistrettoPoint::random(&mut OsRng),
                )
            })
            .collect::<Vec<_>>();

        // Lets build our outputs
        for &idx in &[1, 3, 6] {
            let privkey = Scalar::random(&mut OsRng);
            let pubkey = RistrettoPoint::random(&mut OsRng);
            let amount = 6600;
            let blind_spend = Scalar::random(&mut OsRng);
            let blind_mint = Scalar::random(&mut OsRng);
            let spend = SpendSecret::new(privkey, amount, blind_spend);
            let mint = MintSecret::new(pubkey, amount, blind_mint);
            ring[idx] = spend.output();
            prover.push_spend(spend);
            prover.push_mint(mint);
        }

        // Generate the proof
        let proof = prover
            .prove(&mut Transcript::new(b"Arcturus-Test"), &ring[..])
            .unwrap();

        // Test the proof verifies successfully
        let mut t = Transcript::new(b"Arcturus-Test");
        assert!(verify(&mut t, 2, 5, 8, &ring[..], ring.len(), &[(proof, &[0])]).is_ok());
    }

    struct ComputePJTest {
        k: usize,
        l: usize,
        out_bytes: [[u8; 32]; 4],
    }
    const COMPUTE_P_J_TESTS: [ComputePJTest; 1] = [ComputePJTest {
        k: 2,
        l: 3,
        out_bytes: [
            [
                72, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ],
            [
                78, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ],
            [
                27, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ],
            [
                3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0,
            ],
        ],
    }];

    #[test]
    fn test_compute_p_j() {
        // Just some static a_ji
        let a_ji = (1..5)
            .map(|m| (1..5).map(|n| Scalar::from((m * n) as u32)).collect())
            .collect::<Vec<Vec<Scalar>>>();

        // Compare hard-coded test cases evaluated using a_ji
        for test in &COMPUTE_P_J_TESTS {
            let scalars = compute_p_j(test.k, test.l, &a_ji);
            for (bytes, scalar) in izip!(&test.out_bytes[..], scalars) {
                assert_eq!(bytes, &scalar.to_bytes());
            }
        }
    }
}
