#![allow(non_snake_case)]
use crate::errors::{ArcturusError, ArcturusResult};
use crate::generators::Generators;
use crate::output::Output;
use crate::proof::Proof;
use crate::transcript::TranscriptProtocol;
use crate::util::{exp_iter, sized_flatten, RadixDecomposer};
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use core::iter::{once, repeat, Iterator};
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::IsIdentity;
use curve25519_dalek::traits::VartimeMultiscalarMul;
use itertools::izip;
use merlin::Transcript;
use rand::thread_rng;
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

#[derive(Debug, Clone)]
pub struct Verifier<'a> {
    gens: Generators,
    output_set: Option<&'a [Output]>,
    proofs: Vec<Proof>,
}

impl<'a> Verifier<'a> {
    pub fn new(n: usize, m: usize, w: usize) -> ArcturusResult<Verifier<'a>> {
        let gens = Generators::new(n, m, w)?;
        let proofs = Vec::new();
        Ok(Verifier {
            gens,
            proofs,
            output_set: None,
        })
    }

    /// Returns the ring size required for proof/verification.
    pub fn ring_size(&self) -> usize {
        self.gens.ring_size()
    }

    pub fn load_output_set(&mut self, set: &'a [Output]) -> ArcturusResult<()> {
        if self.gens.ring_size() > set.len() {
            Err(ArcturusError::TooShort)
        } else if self.output_set.is_some() {
            Err(ArcturusError::SetAlreadyLoaded)
        } else {
            self.output_set = Some(set);
            Ok(())
        }
    }

    pub fn clear_output_set(&mut self) {
        self.output_set = None;
    }

    pub fn push_proof(&mut self, proof: Proof) -> ArcturusResult<()> {
        if proof.X_j.len() != self.gens.m
            || proof.Y_j.len() != self.gens.m
            || proof.Z_j.len() != self.gens.m
            || proof.f_uji.len() != proof.J_u.len()
            || proof.zR_u.len() != proof.J_u.len()
        {
            return Err(ArcturusError::InvalidDimensions);
        }
        for f in flatten_3d!(&proof.f_uji) {
            if !f.is_canonical() {
                return Err(ArcturusError::InvalidScalar);
            }
        }
        for zR in &proof.zR_u {
            if !zR.is_canonical() {
                return Err(ArcturusError::InvalidScalar);
            }
        }
        if !proof.zA.is_canonical() || !proof.zC.is_canonical() || !proof.zS.is_canonical() {
            return Err(ArcturusError::InvalidScalar);
        }

        // All checks passed. Push the proof and return Ok()
        self.proofs.push(proof);
        Ok(())
    }

    pub fn pop_proof(&mut self) -> Option<Proof> {
        self.proofs.pop()
    }

    pub fn verify(&self, tscp: &mut Transcript) -> ArcturusResult<()> {
        if let None = self.output_set {
            return Err(ArcturusError::MissingOutputSet);
        }

        let n = self.gens.n;
        let m = self.gens.m;
        tscp.arcturus_domain_sep(n as u64, m as u64);

        // Compute `x` and `mu_k` for each proof
        let mut mu_pk = Vec::with_capacity(self.proofs.len());
        let mut x_p = Vec::with_capacity(self.proofs.len());
        for p in &self.proofs {
            let mut t = tscp.clone();
            for O in &p.mints {
                t.validate_and_append_point(b"pubkey", &O.pubkey.compress())?;
                t.validate_and_append_point(b"commit", &O.commit.compress())?;
            }
            t.validate_and_append_point(b"A", &p.A.compress())?;
            t.validate_and_append_point(b"B", &p.B.compress())?;
            t.validate_and_append_point(b"C", &p.C.compress())?;
            t.validate_and_append_point(b"D", &p.D.compress())?;
            for J in &p.J_u {
                t.validate_and_append_point(b"J", &J.compress())?;
            }
            let mut mu_k = exp_iter(t.challenge_scalar(b"mu"));
            mu_k.next(); // Skip mu^0
            mu_pk.push(mu_k.take(self.gens.ring_size()).collect::<Vec<_>>());
            for X in &p.X_j {
                t.validate_and_append_point(b"X", &X.compress())?;
            }
            for Y in &p.Y_j {
                t.validate_and_append_point(b"Y", &Y.compress())?;
            }
            for Z in &p.Z_j {
                t.validate_and_append_point(b"Z", &Z.compress())?;
            }
            x_p.push(t.challenge_scalar(b"x"));
        }

        let u_max = self.proofs.iter().map(|p| p.f_uji.len()).max().unwrap();

        // To efficiently verify a proof in a single multiexponentiation, each
        // inequality in the protocol is joined into one large inequality. To
        // prevent an attacker from selecting terms that break the
        // relationships guaranteed by the individual inequalities, the
        // verifier must randomly weight each of the terms. Similarly, since we
        // also verify multiple proofs in batch, the terms from each proof must
        // have unique weights as well.
        //
        // See the below resources for more explanation:
        //   * https://github.com/cargodog/arcturus/issues/28
        //   * https://eprint.iacr.org/2017/1066
        //
        // Accordingly, we generate 5 random weights for each of the 5
        // inequalities in this proof protocol, for each proof being verified.
        // Subsequently, all terms pertaining to the first proof proof and the
        // second inequality (labeled (2) in the Arcuturs paper), will be
        // weighted by `wt_[0][1].
        let mut rng = tscp.build_rng().finalize(&mut thread_rng());
        let wt_pn = (0..self.proofs.len())
            .map(|_| (0..5).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();

        // Join f_puj0 & each of p.f_uji to create f_puji
        let f_puji = izip!(&self.proofs, &x_p)
            .map(|(p, x)| {
                p.f_uji
                    .iter()
                    .map(|f_ji| {
                        f_ji.iter()
                            .map(|f_i| {
                                once(x - f_i.iter().sum::<Scalar>())
                                    .chain(f_i.iter().cloned())
                                    .collect::<Vec<_>>()
                            })
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Evaluate each tensor polynomial
        let f_poly_pk = f_puji
            .iter()
            .map(|f_uji| {
                CycleTensorPolyEvals::new(&f_uji, 0)
                    .take(self.gens.ring_size())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Each of equations (1), (2), (3), (4), & (5) are comprised of terms of point
        // multiplications. Below we collect each point to be multiplied, and compute the
        // aggregated scalar factors by which to multiply each point.

        // First, collect all points used in each proof
        let points_G = once(&self.gens.G);
        let points_U = once(&self.gens.U);
        let points_H_uji = flatten_3d!(&self.gens.H_uji[0..u_max]);
        let points_A_p = self.proofs.iter().map(|p| &p.A);
        let points_B_p = self.proofs.iter().map(|p| &p.B);
        let points_C_p = self.proofs.iter().map(|p| &p.C);
        let points_D_p = self.proofs.iter().map(|p| &p.D);
        let points_X_pj = sized_flatten(self.proofs.iter().map(|p| p.X_j.iter()));
        let points_Y_pj = sized_flatten(self.proofs.iter().map(|p| p.Y_j.iter()));
        let points_Z_pj = sized_flatten(self.proofs.iter().map(|p| p.Z_j.iter()));
        let points_J_pu = sized_flatten(self.proofs.iter().map(|p| p.J_u.iter()));
        let points_Q_pt = sized_flatten(
            self.proofs
                .iter()
                .map(|p| p.mints.iter().map(|O| &O.commit)),
        );
        let points_M_k = self
            .output_set
            .unwrap()
            .iter()
            .take(self.gens.ring_size())
            .map(|O| &O.pubkey);
        let points_P_k = self
            .output_set
            .unwrap()
            .iter()
            .take(self.gens.ring_size())
            .map(|O| &O.commit);

        // Chain all points into a single iterator
        let points = points_G
            .chain(points_U)
            .chain(points_H_uji)
            .chain(points_A_p)
            .chain(points_B_p)
            .chain(points_C_p)
            .chain(points_D_p)
            .chain(points_X_pj)
            .chain(points_Y_pj)
            .chain(points_Z_pj)
            .chain(points_J_pu)
            .chain(points_Q_pt)
            .chain(points_M_k)
            .chain(points_P_k);

        // Next, collect all scalar factors to be multiplied with the aforementioned points
        let scalars_G = once(
            izip!(&self.proofs, &wt_pn)
                .map(|(p, wt_n)| wt_n[0] * p.zA)
                .sum::<Scalar>()
                + izip!(&self.proofs, &wt_pn)
                    .map(|(p, wt_n)| wt_n[1] * p.zC)
                    .sum::<Scalar>()
                - izip!(&self.proofs, &wt_pn)
                    .map(|(p, wt_n)| wt_n[2] * p.zR_u.iter().sum::<Scalar>())
                    .sum::<Scalar>()
                - izip!(&self.proofs, &wt_pn)
                    .map(|(p, wt_n)| wt_n[4] * p.zS)
                    .sum::<Scalar>(),
        );
        let scalars_U = once(
            izip!(&mu_pk, &f_poly_pk, &wt_pn)
                .map(|(mu_k, f_poly_k, wt_n)| {
                    izip!(mu_k, f_poly_k)
                        .map(|(mu, f_poly)| wt_n[3] * mu * f_poly)
                        .sum::<Scalar>()
                })
                .sum::<Scalar>(),
        );
        let scalars_H_uji = (0..n * m * u_max).map(|l| {
            izip!(&f_puji, &x_p, &wt_pn)
                .map(|(f_uji, x, wt_n)| {
                    let f = f_uji
                        .iter()
                        .flat_map(|f_ji| f_ji.iter())
                        .flat_map(|f_i| f_i.iter())
                        .nth(l)
                        .unwrap();
                    wt_n[0] * f + wt_n[1] * f * (x - f) // Combination of terms from equations (1) & (2)
                })
                .sum::<Scalar>()
        });

        let scalars_A_p = wt_pn.iter().map(|wt_n| -wt_n[0]);
        let scalars_B_p = izip!(&wt_pn, &x_p).map(|(wt_n, x)| -wt_n[0] * x);
        let scalars_C_p = izip!(&wt_pn, &x_p).map(|(wt_n, x)| -wt_n[1] * x);
        let scalars_D_p = wt_pn.iter().map(|wt_n| -wt_n[1]);
        let scalars_X_pj = sized_flatten(
            izip!(&x_p, &wt_pn).map(|(&x, wt_n)| exp_iter(x).take(m).map(move |xj| -wt_n[2] * xj)),
        );
        let scalars_Y_pj = sized_flatten(
            izip!(&x_p, &wt_pn).map(|(&x, wt_n)| exp_iter(x).take(m).map(move |xj| -wt_n[3] * xj)),
        );
        let scalars_Z_pj = sized_flatten(
            izip!(&x_p, &wt_pn).map(|(&x, wt_n)| exp_iter(x).take(m).map(move |xj| -wt_n[4] * xj)),
        );
        let scalars_J_pu = sized_flatten(
            izip!(&self.proofs, &wt_pn).map(|(p, wt_n)| p.zR_u.iter().map(move |zR| -wt_n[3] * zR)),
        );
        let scalars_Q_pt = sized_flatten(izip!(&self.proofs, &x_p, &wt_pn).map(|(p, &x, wt_n)| {
            repeat(-wt_n[4] * exp_iter(x).nth(m).unwrap()).take(p.mints.len())
        }));
        let scalars_M_k = (0..self.gens.ring_size()).map(|k| {
            izip!(&mu_pk, &f_poly_pk, &wt_pn)
                .map(|(mu_k, f_poly_k, wt_n)| wt_n[2] * mu_k[k] * f_poly_k[k])
                .sum()
        });
        let scalars_P_k = (0..self.gens.ring_size()).map(|k| {
            izip!(&f_poly_pk, &wt_pn)
                .map(|(f_poly_k, wt_n)| wt_n[4] * f_poly_k[k])
                .sum()
        });

        // Chain all scalar factors into single iterator
        let scalars = scalars_G
            .chain(scalars_U)
            .chain(scalars_H_uji)
            .chain(scalars_A_p)
            .chain(scalars_B_p)
            .chain(scalars_C_p)
            .chain(scalars_D_p)
            .chain(scalars_X_pj)
            .chain(scalars_Y_pj)
            .chain(scalars_Z_pj)
            .chain(scalars_J_pu)
            .chain(scalars_Q_pt)
            .chain(scalars_M_k)
            .chain(scalars_P_k);

        // Evaluate everything as a single multiscalar multiplication
        if RistrettoPoint::vartime_multiscalar_mul(scalars, points).is_identity() {
            return Ok(());
        } else {
            return Err(ArcturusError::VerificationFailed);
        }
    }
}

struct CycleTensorPolyEvals<'a> {
    w: usize,
    m: usize,
    n: usize,
    f_uji: &'a Vec<Vec<Vec<Scalar>>>,
    partial_digits_j: Vec<usize>,
    partial_prods_ju: Vec<Vec<Scalar>>,
}

impl<'a> CycleTensorPolyEvals<'a> {
    fn new(f_uji: &'a Vec<Vec<Vec<Scalar>>>, start: usize) -> CycleTensorPolyEvals<'a> {
        let w = f_uji.len();
        let m = f_uji[0].len();
        let n = f_uji[0][0].len();
        let partial_digits_j = vec![0; m];
        let partial_prods_ju = vec![vec![Scalar::one(); w]; m];
        let mut eval_iter = CycleTensorPolyEvals {
            w,
            m,
            n,
            f_uji,
            partial_digits_j,
            partial_prods_ju,
        };
        eval_iter.set_position(start);
        eval_iter
    }

    fn set_position(&mut self, pos: usize) {
        // Decompose new position into stored digits
        for (j, d) in RadixDecomposer::new(pos, self.n).take(self.m).enumerate() {
            self.partial_digits_j[self.m - j - 1] = d;
        }

        // Update partial products
        for u in 0..self.w {
            self.partial_prods_ju[0][u] = self.f_uji[u][self.m - 1][self.partial_digits_j[0]];
        }
        for j in 1..self.m {
            for u in 0..self.w {
                let prev_part = self.partial_prods_ju[j - 1][u];
                self.partial_prods_ju[j][u] =
                    prev_part * self.f_uji[u][self.m - j - 1][self.partial_digits_j[j]];
            }
        }
    }

    // Recursively multiply the factors corresponding to each digit of k
    fn update(&mut self) {
        if let Some(mut i) = self.partial_digits_j.pop() {
            i += 1;
            if i >= self.n {
                self.update();
            } else {
                let j = self.partial_digits_j.len();
                for u in 0..self.w {
                    self.partial_prods_ju[j][u] = self.f_uji[u][self.m - j - 1][i];
                }
                if j > 0 {
                    for u in 0..self.w {
                        let prev_part = self.partial_prods_ju[j - 1][u];
                        self.partial_prods_ju[j][u] *= prev_part;
                    }
                }
                self.partial_digits_j.push(i);
            }
        }
        for j in self.partial_digits_j.len()..self.m {
            self.partial_digits_j.push(0);
            for u in 0..self.w {
                self.partial_prods_ju[j][u] = self.f_uji[u][self.m - j - 1][0];
            }
            if j > 0 {
                for u in 0..self.w {
                    let prev_part = self.partial_prods_ju[j - 1][u];
                    self.partial_prods_ju[j][u] *= prev_part;
                }
            }
        }
    }
}

impl Iterator for CycleTensorPolyEvals<'_> {
    type Item = Scalar;

    #[inline]
    fn next(&mut self) -> Option<Scalar> {
        let eval_sum = self.partial_prods_ju.last().unwrap().iter().sum::<Scalar>();
        self.update();
        Some(eval_sum)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::output::*;
    use crate::prover::*;
    use rand::rngs::OsRng; // You should use a more secure RNG

    #[test]
    fn verify_2x5() {
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
        let mut verifier = Verifier::new(2, 5, 8).unwrap();
        verifier.load_output_set(&ring[..]).unwrap();
        verifier.push_proof(proof).unwrap();
        let mut t = Transcript::new(b"Arcturus-Test");
        assert!(verifier.verify(&mut t).is_ok());
    }

    #[test]
    fn test_cycle_tensor_poly_evals() {
        // Generate a random f_uji tensor
        let mut rng = rand::thread_rng();
        let f_uji = (0..5)
            .map(|_| {
                (0..4)
                    .map(|_| (0..3).map(|_| Scalar::random(&mut rng)).collect::<Vec<_>>())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Test the iterator starting at zero
        let mut digits: Vec<usize> = vec![0; f_uji[0].len()];
        for eval in CycleTensorPolyEvals::new(&f_uji, 0).take(81) {
            let mut sum = Scalar::zero();
            for u in 0..f_uji.len() {
                let mut prod = Scalar::one();
                for (j, &i) in digits.iter().enumerate() {
                    prod *= f_uji[u][j][i];
                }
                sum += prod;
            }
            for j in 0..digits.len() {
                digits[j] += 1;
                if digits[j] >= f_uji[0][0].len() {
                    digits[j] = 0;
                } else {
                    break;
                }
            }
            assert_eq!(sum, eval);
        }

        // Now test the iterator at an offset and compare
        let mut iter0 = CycleTensorPolyEvals::new(&f_uji, 0).take(81);
        iter0.nth(4); // Skip first 5
        let mut iter5 = CycleTensorPolyEvals::new(&f_uji, 5).take(81); // Same iterator, but start at position 5
        for (i0, i5) in izip!(&mut iter0, &mut iter5) {
            assert_eq!(i0, i5); // Each should match until iter0 runs out
        }

        // Now reset iter0, and check that last 5 of iter5 match first 5 of iter0
        let mut iter0 = CycleTensorPolyEvals::new(&f_uji, 0).take(81);
        for (i0, i5) in izip!(&mut iter0, &mut iter5) {
            assert_eq!(i0, i5);
        }
    }
}
