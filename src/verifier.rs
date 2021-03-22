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

pub fn verify(
    tscp: &mut Transcript,
    n: usize,
    m: usize,
    w: usize,
    output_set: &[Output],
    bin_size: usize,
    proofs: &[(Proof, &[usize])],
) -> ArcturusResult<()> {
    let mut verifier = begin_verification(n, m, w, bin_size)?;
    for (proof, bins) in proofs {
        verifier.add_proof(proof.clone(), bins)?;
    }
    let (mut verifier, jobs) = verifier.polynomial_stage(tscp)?;
    for job in jobs {
        verifier.process_job(job)?;
    }
    let (mut verifier, jobs) = verifier.ring_stage(output_set)?;
    for job in jobs {
        verifier.process_job(job)?;
    }
    verifier.finalize()
}

pub fn begin_verification(
    n: usize,
    m: usize,
    w: usize,
    bin_size: usize,
) -> ArcturusResult<CollectStage> {
    CollectStage::new(n, m, w, bin_size)
}

#[derive(Debug, Clone)]
pub struct CollectStage {
    gens: Generators,
    bin_size: usize,
    proofs_p: Vec<Proof>,
    bins_pb: Vec<Vec<usize>>,
}

impl CollectStage {
    pub fn new(n: usize, m: usize, w: usize, bin_size: usize) -> ArcturusResult<Self> {
        let gens = Generators::new(n, m, w)?;
        Ok(CollectStage {
            gens,
            bin_size,
            proofs_p: Vec::new(),
            bins_pb: Vec::new(),
        })
    }

    pub fn add_proof(&mut self, proof: Proof, bins: &[usize]) -> ArcturusResult<()> {
        // Check the proof for obvious errors
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
        if self.gens.ring_size() > self.bin_size * bins.len() {
            return Err(ArcturusError::TooFewBins);
        }
        if self.gens.ring_size() < self.bin_size * bins.len() {
            return Err(ArcturusError::TooManyBins);
        }
        for b in 0..bins.len() {
            if bins[b + 1..].iter().any(|&bin| bin == bins[b]) {
                return Err(ArcturusError::DuplicateBins);
            }
        }

        // All checks passed. Add the proof to be verified.
        self.proofs_p.push(proof);
        self.bins_pb.push(Vec::from(bins));
        Ok(())
    }

    pub fn polynomial_stage(
        self,
        tscp: &mut Transcript,
    ) -> ArcturusResult<(PolynomialStage, Vec<PolynomialJob>)> {
        tscp.arcturus_domain_sep(self.gens.n as u64, self.gens.m as u64);

        let mut jobs = Vec::with_capacity(self.proofs_p.len());
        for (proof, bins_b) in izip!(self.proofs_p, self.bins_pb) {
            let mut t = tscp.clone();
            for O in &proof.mints {
                t.validate_and_append_point(b"pubkey", &O.pubkey.compress())?;
                t.validate_and_append_point(b"commit", &O.commit.compress())?;
            }
            t.validate_and_append_point(b"A", &proof.A.compress())?;
            t.validate_and_append_point(b"B", &proof.B.compress())?;
            t.validate_and_append_point(b"C", &proof.C.compress())?;
            t.validate_and_append_point(b"D", &proof.D.compress())?;
            for J in &proof.J_u {
                t.validate_and_append_point(b"J", &J.compress())?;
            }
            let mut mu_k = exp_iter(t.challenge_scalar(b"mu"));
            mu_k.next(); // Skip mu^0
            let mu_k = mu_k.take(self.gens.ring_size()).collect::<Vec<_>>();
            for X in &proof.X_j {
                t.validate_and_append_point(b"X", &X.compress())?;
            }
            for Y in &proof.Y_j {
                t.validate_and_append_point(b"Y", &Y.compress())?;
            }
            for Z in &proof.Z_j {
                t.validate_and_append_point(b"Z", &Z.compress())?;
            }
            let x = t.challenge_scalar(b"x");

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
            let mut rng = tscp.build_rng().finalize(&mut thread_rng());
            let eq_wts = (0..5).map(|_| Scalar::random(&mut rng)).collect();

            jobs.push(PolynomialJob {
                proof,
                eq_wts,
                x,
                mu_k,
                bins_b,
                f_uji: Vec::new(),
                f_poly_k: Vec::new(),
            });
        }
        let stage = PolynomialStage {
            gens: self.gens,
            bin_size: self.bin_size,
            jobs_p: Vec::with_capacity(jobs.len()),
        };

        Ok((stage, jobs))
    }
}

#[derive(Debug, Clone)]
pub struct PolynomialJob {
    proof: Proof,
    eq_wts: Vec<Scalar>,
    x: Scalar,
    mu_k: Vec<Scalar>,
    bins_b: Vec<usize>,
    f_uji: Vec<Vec<Vec<Scalar>>>,
    f_poly_k: Vec<Scalar>,
}

#[derive(Debug, Clone)]
pub struct PolynomialStage {
    gens: Generators,
    bin_size: usize,
    jobs_p: Vec<PolynomialJob>,
}

impl PolynomialStage {
    pub fn process_job(&mut self, mut job: PolynomialJob) -> ArcturusResult<()> {
        // Join f_uj0 & each of proof.f_uji to create f_uji
        job.f_uji = job
            .proof
            .f_uji
            .iter()
            .map(|f_ji| {
                f_ji.iter()
                    .map(|f_i| {
                        once(job.x - f_i.iter().sum::<Scalar>())
                            .chain(f_i.iter().cloned())
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Evaluate each tensor polynomial
        job.f_poly_k = CycleTensorPolyEvals::new(&job.f_uji.as_ref(), 0)
            .take(self.gens.ring_size())
            .collect::<Vec<_>>();

        self.jobs_p.push(job);
        Ok(())
    }

    pub fn ring_stage(self, output_set: &[Output]) -> ArcturusResult<(RingStage, Vec<RingJob>)> {
        let u_max = self.jobs_p.iter().map(|j| j.f_uji.len()).max().unwrap();

        // Now evaluate all multiplications for terms which do not iterate over 'k'.
        // The 'k' terms will be evaluated later in bins.

        // First, collect all points used in each proof
        let points_G = once(&self.gens.G);
        let points_H_uji = flatten_3d!(&self.gens.H_uji[0..u_max]);
        let points_A_p = self.jobs_p.iter().map(|job| &job.proof.A);
        let points_B_p = self.jobs_p.iter().map(|job| &job.proof.B);
        let points_C_p = self.jobs_p.iter().map(|job| &job.proof.C);
        let points_D_p = self.jobs_p.iter().map(|job| &job.proof.D);
        let points_X_pj = sized_flatten(self.jobs_p.iter().map(|job| job.proof.X_j.iter()));
        let points_Y_pj = sized_flatten(self.jobs_p.iter().map(|job| job.proof.Y_j.iter()));
        let points_Z_pj = sized_flatten(self.jobs_p.iter().map(|job| job.proof.Z_j.iter()));
        let points_J_pu = sized_flatten(self.jobs_p.iter().map(|job| job.proof.J_u.iter()));
        let points_Q_pt = sized_flatten(
            self.jobs_p
                .iter()
                .map(|job| job.proof.mints.iter().map(|O| &O.commit)),
        );

        // Chain all points into a single iterator
        let points = points_G
            .chain(points_H_uji)
            .chain(points_A_p)
            .chain(points_B_p)
            .chain(points_C_p)
            .chain(points_D_p)
            .chain(points_X_pj)
            .chain(points_Y_pj)
            .chain(points_Z_pj)
            .chain(points_J_pu)
            .chain(points_Q_pt);

        // Next, collect all scalar factors to be multiplied with the aforementioned points
        let scalars_G = once(
            self.jobs_p
                .iter()
                .map(|job| job.eq_wts[0] * job.proof.zA)
                .sum::<Scalar>()
                + self
                    .jobs_p
                    .iter()
                    .map(|job| job.eq_wts[1] * job.proof.zC)
                    .sum::<Scalar>()
                - self
                    .jobs_p
                    .iter()
                    .map(|job| job.eq_wts[2] * job.proof.zR_u.iter().sum::<Scalar>())
                    .sum::<Scalar>()
                - self
                    .jobs_p
                    .iter()
                    .map(|job| job.eq_wts[4] * job.proof.zS)
                    .sum::<Scalar>(),
        );
        let scalars_H_uji = (0..self.gens.n * self.gens.m * u_max).map(|l| {
            self.jobs_p
                .iter()
                .map(|job| {
                    let f = job
                        .f_uji
                        .iter()
                        .flat_map(|f_ji| f_ji.iter())
                        .flat_map(|f_i| f_i.iter())
                        .nth(l)
                        .unwrap();
                    job.eq_wts[0] * f + job.eq_wts[1] * f * (job.x - f) // Combination of terms from equations (1) & (2)
                })
                .sum::<Scalar>()
        });

        let scalars_A_p = self.jobs_p.iter().map(|job| -job.eq_wts[0]);
        let scalars_B_p = self.jobs_p.iter().map(|job| -job.eq_wts[0] * job.x);
        let scalars_C_p = self.jobs_p.iter().map(|job| -job.eq_wts[1] * job.x);
        let scalars_D_p = self.jobs_p.iter().map(|job| -job.eq_wts[1]);
        let scalars_X_pj = sized_flatten(self.jobs_p.iter().map(|job| {
            exp_iter(job.x)
                .take(self.gens.m)
                .map(move |xj| -job.eq_wts[2] * xj)
        }));
        let scalars_Y_pj = sized_flatten(self.jobs_p.iter().map(|job| {
            exp_iter(job.x)
                .take(self.gens.m)
                .map(move |xj| -job.eq_wts[3] * xj)
        }));
        let scalars_Z_pj = sized_flatten(self.jobs_p.iter().map(|job| {
            exp_iter(job.x)
                .take(self.gens.m)
                .map(move |xj| -job.eq_wts[4] * xj)
        }));
        let scalars_J_pu = sized_flatten(
            self.jobs_p
                .iter()
                .map(|job| job.proof.zR_u.iter().map(move |zR| -job.eq_wts[3] * zR)),
        );
        let scalars_Q_pt = sized_flatten(self.jobs_p.iter().map(|job| {
            repeat(-job.eq_wts[4] * exp_iter(job.x).nth(self.gens.m).unwrap())
                .take(job.proof.mints.len())
        }));

        // Chain all scalar factors into single iterator
        let scalars = scalars_G
            .chain(scalars_H_uji)
            .chain(scalars_A_p)
            .chain(scalars_B_p)
            .chain(scalars_C_p)
            .chain(scalars_D_p)
            .chain(scalars_X_pj)
            .chain(scalars_Y_pj)
            .chain(scalars_Z_pj)
            .chain(scalars_J_pu)
            .chain(scalars_Q_pt);

        // Evaluate everything as a single multiscalar multiplication
        let partial_eval = RistrettoPoint::vartime_multiscalar_mul(scalars, points);

        // Next, collect all points for terms that iterate over 'k'. This terms will be
        // divided into bins, to allow parallel processing
        let num_bins = self.gens.ring_size() / self.bin_size;
        assert_eq!(self.gens.ring_size(), num_bins * self.bin_size);
        let mut jobs = Vec::with_capacity(num_bins);
        for (b, (bin_outputs, jobs_p)) in izip!(
            output_set.chunks(self.bin_size),
            (0..num_bins).map(|b| self
                .jobs_p
                .iter()
                .filter(move |job| job.bins_b.iter().any(|&bin| bin == b)))
        ).enumerate() {
            let points_M_k = bin_outputs
                .iter()
                .take(self.gens.ring_size())
                .map(|O| O.pubkey);
            let points_U = once(self.gens.U);
            let points_P_k = bin_outputs
                .iter()
                .take(self.gens.ring_size())
                .map(|O| O.commit);

            // Chain all points into a single iterator
            let points = points_M_k
                .chain(points_U)
                .chain(points_P_k)
                .collect::<Vec<_>>();

            // Next, collect all scalar factors to be multiplied with the aforementioned points
            let offset = b * self.bin_size;
            let scalars_M_k = (0..self.gens.ring_size())
                .skip(offset)
                .take(self.bin_size)
                .map(|k| {
                jobs_p
                    .clone()
                    .map(|job| job.eq_wts[2] * job.mu_k[k] * job.f_poly_k[k])
                    .sum()
            });
            let scalars_U = once(
                jobs_p
                    .clone()
                    .map(|job| {
                        izip!(&job.mu_k, &job.f_poly_k)
                            .skip(offset)
                            .take(self.bin_size)
                            .map(|(mu, f_poly)| job.eq_wts[3] * mu * f_poly)
                            .sum::<Scalar>()
                    })
                    .sum::<Scalar>(),
            );
            let scalars_P_k = (0..self.gens.ring_size())
                .skip(offset)
                .take(self.bin_size)
                .map(|k| {
                jobs_p
                    .clone()
                    .map(|job| job.eq_wts[4] * job.f_poly_k[k])
                    .sum()
            });

            // Chain all scalar factors into single iterator
            let scalars = scalars_M_k
                .chain(scalars_U)
                .chain(scalars_P_k)
                .collect::<Vec<_>>();

            jobs.push(RingJob { scalars, points });
        }
        let stage = RingStage { partial_eval };
        Ok((stage, jobs))
    }
}

#[derive(Debug, Clone)]
pub struct RingJob {
    scalars: Vec<Scalar>,
    points: Vec<RistrettoPoint>,
}

#[derive(Debug, Clone)]
pub struct RingStage {
    partial_eval: RistrettoPoint,
}

impl RingStage {
    pub fn process_job(&mut self, job: RingJob) -> ArcturusResult<()> {
        self.partial_eval += RistrettoPoint::vartime_multiscalar_mul(job.scalars, job.points);
        Ok(())
    }

    pub fn finalize(self) -> ArcturusResult<()> {
        if self.partial_eval.is_identity() {
            Ok(())
        } else {
            Err(ArcturusError::VerificationFailed)
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
        let mut t = Transcript::new(b"Arcturus-Test");
        assert!(verify(&mut t, 2, 5, 8, &ring[..], ring.len()/4, &[(proof, &[0, 1, 2, 3])]).is_ok());
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
