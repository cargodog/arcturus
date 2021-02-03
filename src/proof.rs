#![allow(non_snake_case)]
use crate::errors::{ArcturusError, ArcturusResult};
use crate::transcript::TranscriptProtocol;
use crate::util::{exp_iter, SizedFlatten};
#[cfg(not(feature = "std"))]
use alloc::vec::Vec;
use blake2::Blake2b;
use core::iter::{once, repeat, Iterator};
use curve25519_dalek::constants;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, MultiscalarMul, VartimeMultiscalarMul};
use itertools::izip;
use merlin::Transcript;
use polynomials::Polynomial;
use rand::thread_rng;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
#[cfg(feature = "std")]
use std::vec::Vec;

/// An output consists of a public key and a value commitment
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Output {
    pubkey: RistrettoPoint,
    commit: RistrettoPoint,
}

impl Output {
    pub fn new(pubkey: RistrettoPoint, commit: RistrettoPoint) -> Self {
        Output { pubkey, commit }
    }
}

/// Secret data needed to spend an existing [`Output`]
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct SpendSecret {
    privkey: Scalar,
    amount: Scalar,
    blind: Scalar,
}

impl SpendSecret {
    pub fn new(privkey: Scalar, amount: u64, blind: Scalar) -> Self {
        let amount = Scalar::from(amount);
        SpendSecret {
            privkey,
            amount,
            blind,
        }
    }

    pub fn to_output(&self) -> Output {
        let G = constants::RISTRETTO_BASEPOINT_POINT;
        let H = derive_generator(&G, 0, 0, 0);
        let pubkey = self.privkey * G;
        let commit = self.amount * H + self.blind * G;
        Output { pubkey, commit }
    }

    pub fn get_tag(&self) -> RistrettoPoint {
        let G = constants::RISTRETTO_BASEPOINT_POINT;
        let U = RistrettoPoint::hash_from_bytes::<Blake2b>(G.compress().as_bytes());
        self.privkey.invert() * U
    }
}

/// Secret data needed to mint a new [`Output`]
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct MintSecret {
    pubkey: RistrettoPoint,
    amount: Scalar,
    blind: Scalar,
}

impl MintSecret {
    pub fn new(pubkey: RistrettoPoint, amount: u64, blind: Scalar) -> Self {
        let amount = Scalar::from(amount);
        MintSecret {
            pubkey,
            amount,
            blind,
        }
    }

    pub fn to_output(&self) -> Output {
        let G = constants::RISTRETTO_BASEPOINT_POINT;
        let H = derive_generator(&G, 0, 0, 0);
        let pubkey = self.pubkey;
        let commit = self.amount * H + self.blind * G;
        Output { pubkey, commit }
    }
}

/// Zero-knowledge proof that some minted outputs are valid spends of existing outputs in a ring
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ArcturusProof {
    mints: Vec<Output>,
    A: RistrettoPoint,
    B: RistrettoPoint,
    C: RistrettoPoint,
    D: RistrettoPoint,
    X_j: Vec<RistrettoPoint>,
    Y_j: Vec<RistrettoPoint>,
    Z_j: Vec<RistrettoPoint>,
    J_u: Vec<RistrettoPoint>,
    f_uji: Vec<Vec<Vec<Scalar>>>,
    zA: Scalar,
    zC: Scalar,
    zR_u: Vec<Scalar>,
    zS: Scalar,
}

impl ArcturusProof {
    pub fn count_spends(&self) -> usize {
        self.J_u.len()
    }

    pub fn count_mints(&self) -> usize {
        self.mints.len()
    }

    pub fn spend_tags(&self) -> Vec<RistrettoPoint> {
        self.J_u.clone()
    }

    pub fn mints(&self) -> Vec<Output> {
        self.mints.clone()
    }
}

/// Generators and proof context necessary to prove and verify Arcturus proofs.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ArcturusGens {
    n: usize,
    m: usize,
    w: usize,
    G: RistrettoPoint,
    U: RistrettoPoint,
    H_uji: Vec<Vec<Vec<RistrettoPoint>>>,
}

impl ArcturusGens {
    /// Compute a new set of generators.
    ///
    /// This will precompute the generators necessary an `m` digit `n`-ary anonymity set. For
    /// example, if `n = 2`, `m = 8`, the computed generators will support proofs with an anonymity
    /// set of `2^8 = 256`.
    ///
    /// This will also precompute generators for up to `w` signers in a proof.
    pub fn new(n: usize, m: usize, w: usize) -> ArcturusResult<ArcturusGens> {
        if n < 2 {
            return Err(ArcturusError::ProofRadixTooSmall);
        }
        if m < 2 {
            return Err(ArcturusError::ProofDigitsTooSmall);
        }
        if w < 1 {
            return Err(ArcturusError::ProofNumSignersTooSmall);
        }
        if let Some(x) = n.checked_pow(m as u32) {
            if x < w {
                return Err(ArcturusError::ProofNumSignersTooLarge);
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

        Ok(ArcturusGens {
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

    /// Create a flattened iterator over a 3D tensor
    fn tensor<'a, T>(&self, t: &'a Vec<Vec<Vec<T>>>, u: usize) -> TensorIterator<'a, T> {
        TensorIterator::new(t, u, self.m, self.n)
    }

    /// Prove that newly minted outputs correctly spend existing outputs within the ring.
    ///
    /// > Note: this does not prove that an output has not been previously spent in a ledger. Each
    /// spent output yields a unique 'spend tag'. To avoid double spends, the verifier should query
    /// this proof for all spend tags, and confirm no spend tag has been used in a previous
    /// transaction.
    pub fn prove(
        &self,
        tscp: &mut Transcript,
        ring: &[Output],
        idxs: &[usize],
        spends: &[SpendSecret],
        mints: &[MintSecret],
    ) -> ArcturusResult<ArcturusProof> {
        tscp.arcturus_domain_sep(self.n as u64, self.m as u64);

        if idxs.len() != spends.len() {
            return Err(ArcturusError::BadArg);
        }

        // First make sure the mints and spends balance to zero
        if spends.iter().map(|s| s.amount).sum::<Scalar>()
            != mints.iter().map(|m| m.amount).sum::<Scalar>()
        {
            return Err(ArcturusError::MintsAndSpendsImbalance);
        }

        let u = idxs.len();

        // Create a `TranscriptRng` from the high-level witness data
        //
        // The prover wants to rekey the RNG with its witness data (`l`and `r`).
        let mut rng = {
            let mut builder = tscp.build_rng();
            for &i in idxs {
                builder =
                    builder.rekey_with_witness_bytes(b"idx", Scalar::from(i as u32).as_bytes());
            }
            for s in spends {
                builder = builder.rekey_with_witness_bytes(b"privkey", s.privkey.as_bytes());
                builder = builder.rekey_with_witness_bytes(b"amount", s.amount.as_bytes());
                builder = builder.rekey_with_witness_bytes(b"blind", s.blind.as_bytes());
            }
            for m in mints {
                builder = builder.rekey_with_witness_bytes(b"amount", m.amount.as_bytes());
                builder = builder.rekey_with_witness_bytes(b"blind", m.blind.as_bytes());
            }
            builder.finalize(&mut thread_rng())
        };

        let mut a_uji = (0..u)
            .map(|_| {
                (0..self.m)
                    .map(|_| (1..self.n).map(|_| Scalar::random(&mut rng)).collect())
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
            once(&rA).chain(self.tensor(&a_uji, u)),
            once(&self.G).chain(self.tensor(&self.H_uji, u)),
        );

        // Convert each index from binary to a `m` digit `n-ary` number
        let sigma_uji = idxs
            .iter()
            .map(|&l| {
                convert_base(l, self.n, self.m)
                    .iter()
                    .map(|&l_j| {
                        let mut l_ji = vec![Scalar::zero(); self.n - 1];
                        l_ji.insert(l_j, Scalar::one());
                        l_ji
                    })
                    .collect()
            })
            .collect::<Vec<Vec<Vec<_>>>>();

        // B = Com(sigma, rB) = rB*G + sigma_uji*H_uji
        let rB = Scalar::random(&mut rng);
        let B = RistrettoPoint::multiscalar_mul(
            once(&rB).chain(self.tensor(&sigma_uji, u)),
            once(&self.G).chain(self.tensor(&self.H_uji, u)),
        );

        // C = Com(a*(1-2*sigma), rC) = rB*G + (a_uji*(1-2*sigma_uji))*H_uji
        let C_vals_uji = izip!(self.tensor(&sigma_uji, u), self.tensor(&a_uji, u))
            .map(|(sigma, a)| a * (Scalar::one() - Scalar::from(2u32) * sigma));
        let rC = Scalar::random(&mut rng);
        let C = RistrettoPoint::multiscalar_mul(
            once(rC).chain(C_vals_uji),
            once(&self.G).chain(self.tensor(&self.H_uji, u)),
        );

        // D = Com(-a^2, rD) = rD*G + -a_uji*a_uji*H_uji
        let rD = Scalar::random(&mut rng);
        let D = RistrettoPoint::multiscalar_mul(
            once(rD).chain(self.tensor(&a_uji, u).map(|a| -a * a)),
            once(&self.G).chain(self.tensor(&self.H_uji, u)),
        );

        // Generate randomness rho & rhobar
        let rho_uj = (0..u)
            .map(|_| (0..self.m).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();
        let rhobar_uj = (0..u)
            .map(|_| (0..self.m).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();

        // Compute spend tags
        let J_u = spends.iter().map(|s| s.get_tag()).collect::<Vec<_>>();

        // Compute minted outputs
        let mints_pub = mints.iter().map(|m| m.to_output()).collect::<Vec<_>>();

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
        let mut ring_count = 0;
        let (mut X_j, y_j, mut Z_j) =
            izip!(ring.iter().map(|O| (O.pubkey, O.commit)), mu_k.clone())
                .enumerate()
                .map(|(k, ((M, P), mu))| {
                    ring_count += 1;
                    let p_j = idxs
                        .iter()
                        .enumerate()
                        .map(|(u, &l)| compute_p_j(k, l, &a_uji[u]))
                        .fold(vec![Scalar::zero(); self.m], |mut p_j, p_j_uth| {
                            for j in 0..self.m {
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
                        vec![RistrettoPoint::default(); self.m],
                        vec![Scalar::zero(); self.m],
                        vec![RistrettoPoint::default(); self.m],
                    ),
                    |(mut X_j, mut y_j, mut Z_j), (X_j_kth, y_j_kth, Z_j_kth)| {
                        for j in 0..self.m {
                            X_j[j] += X_j_kth[j];
                            y_j[j] += y_j_kth[j];
                            Z_j[j] += Z_j_kth[j];
                        }
                        (X_j, y_j, Z_j)
                    },
                );
        if ring_count < self.ring_size() {
            return Err(ArcturusError::RingSizeTooSmall);
        }
        if ring_count > self.ring_size() {
            return Err(ArcturusError::RingSizeTooLarge);
        }
        let mut Y_j = y_j.iter().map(|y| y * self.U).collect::<Vec<_>>();
        for j in 0..self.m {
            X_j[j] += rho_uj.iter().map(|rho_j| rho_j[j]).sum::<Scalar>() * self.G;
            Y_j[j] += izip!(&rho_uj, &J_u)
                .map(|(rho_j, J)| rho_j[j] * J)
                .sum::<RistrettoPoint>();
            Z_j[j] += rhobar_uj.iter().map(|rhobar_j| rhobar_j[j]).sum::<Scalar>() * self.G;
        }

        // Commit to remaining public parameters
        for j in 0..self.m {
            tscp.append_point(b"X", &X_j[j].compress());
        }
        for j in 0..self.m {
            tscp.append_point(b"Y", &Y_j[j].compress());
        }
        for j in 0..self.m {
            tscp.append_point(b"Z", &Z_j[j].compress());
        }
        let x = tscp.challenge_scalar(b"x");
        let x_exp_m = exp_iter(x).nth(self.m).unwrap();

        let zA = rA + x * rB;
        let zC = rD + x * rC;
        let f_uji = izip!(&sigma_uji, &a_uji)
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
        let zR_u = izip!(idxs, spends.iter().map(|o| o.privkey), &rho_uj)
            .map(|(&l, r, rho_j)| {
                mu_k.clone().nth(l).unwrap() * r * x_exp_m
                    - izip!(exp_iter(x), rho_j)
                        .map(|(exp_x, rho)| rho * exp_x)
                        .sum::<Scalar>()
            })
            .collect::<Vec<_>>();
        let zS = x_exp_m
            * (spends.iter().map(|s| s.blind).sum::<Scalar>()
                - mints.iter().map(|m| m.blind).sum::<Scalar>())
            - exp_iter(x)
                .take(self.m)
                .enumerate()
                .map(|(j, x_exp_j)| {
                    x_exp_j * rhobar_uj.iter().map(|rhobar_j| rhobar_j[j]).sum::<Scalar>()
                })
                .sum::<Scalar>();

        Ok(ArcturusProof {
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

    /// Verify in zero-knowledge that a proof is valid
    pub fn verify(
        &self,
        tscp: &mut Transcript,
        ring: &[Output],
        proof: ArcturusProof,
    ) -> ArcturusResult<()> {
        self.verify_batch(tscp, ring, &[proof])
    }

    /// Verify in zero-knowledge that a batch of proofs are valid
    pub fn verify_batch(
        &self,
        tscp: &mut Transcript,
        ring: &[Output],
        proofs: &[ArcturusProof],
    ) -> ArcturusResult<()> {
        for p in proofs.iter() {
            if p.X_j.len() != self.m
                || p.Y_j.len() != self.m
                || p.Z_j.len() != self.m
                || p.f_uji.len() != p.J_u.len()
                || p.zR_u.len() != p.J_u.len()
            {
                return Err(ArcturusError::VerificationFailed);
            }
        }

        tscp.arcturus_domain_sep(self.n as u64, self.m as u64);

        // Compute `x` and `mu_k` for each proof
        let mut mu_pk = Vec::with_capacity(proofs.len());
        let mut x_p = Vec::with_capacity(proofs.len());
        for p in proofs {
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
            mu_pk.push(mu_k.take(self.ring_size()).collect::<Vec<_>>());
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

        let u_max = proofs.iter().map(|p| p.f_uji.len()).max().unwrap();

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
        let wt_pn = (0..proofs.len())
            .map(|_| (0..5).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();

        // Join f_puj0 & each of p.f_uji to create f_puji
        let f_puji = izip!(proofs, &x_p)
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
                cycle_tensor_poly_evals(&f_uji)
                    .take(self.ring_size())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Each of equations (1), (2), (3), (4), & (5) are comprised of terms of point
        // multiplications. Below we collect each point to be multiplied, and compute the
        // aggregated scalar factors by which to multiply each point.

        // First, collect all points used in each proof
        let points_G = once(&self.G);
        let points_U = once(&self.U);
        let points_H_uji = self.tensor(&self.H_uji, u_max);
        let points_A_p = proofs.iter().map(|p| &p.A);
        let points_B_p = proofs.iter().map(|p| &p.B);
        let points_C_p = proofs.iter().map(|p| &p.C);
        let points_D_p = proofs.iter().map(|p| &p.D);
        let points_X_pj = SizedFlatten::new(proofs.iter().map(|p| p.X_j.iter()));
        let points_Y_pj = SizedFlatten::new(proofs.iter().map(|p| p.Y_j.iter()));
        let points_Z_pj = SizedFlatten::new(proofs.iter().map(|p| p.Z_j.iter()));
        let points_J_pu = SizedFlatten::new(proofs.iter().map(|p| p.J_u.iter()));
        let points_Q_pt =
            SizedFlatten::new(proofs.iter().map(|p| p.mints.iter().map(|O| &O.commit)));
        let points_M_k = ring.iter().take(self.ring_size()).map(|O| &O.pubkey);
        let points_P_k = ring.iter().take(self.ring_size()).map(|O| &O.commit);

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
            izip!(proofs, &wt_pn)
                .map(|(p, wt_n)| wt_n[0] * p.zA)
                .sum::<Scalar>()
                + izip!(proofs, &wt_pn)
                    .map(|(p, wt_n)| wt_n[1] * p.zC)
                    .sum::<Scalar>()
                - izip!(proofs, &wt_pn)
                    .map(|(p, wt_n)| wt_n[2] * p.zR_u.iter().sum::<Scalar>())
                    .sum::<Scalar>()
                - izip!(proofs, &wt_pn)
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
        let scalars_H_uji = (0..self.n * self.m * u_max).map(|l| {
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
        let scalars_X_pj = SizedFlatten::new(
            izip!(&x_p, &wt_pn)
                .map(|(&x, wt_n)| exp_iter(x).take(self.m).map(move |xj| -wt_n[2] * xj)),
        );
        let scalars_Y_pj = SizedFlatten::new(
            izip!(&x_p, &wt_pn)
                .map(|(&x, wt_n)| exp_iter(x).take(self.m).map(move |xj| -wt_n[3] * xj)),
        );
        let scalars_Z_pj = SizedFlatten::new(
            izip!(&x_p, &wt_pn)
                .map(|(&x, wt_n)| exp_iter(x).take(self.m).map(move |xj| -wt_n[4] * xj)),
        );
        let scalars_J_pu = SizedFlatten::new(
            izip!(proofs, &wt_pn).map(|(p, wt_n)| p.zR_u.iter().map(move |zR| -wt_n[3] * zR)),
        );
        let scalars_Q_pt = SizedFlatten::new(izip!(proofs, &x_p, &wt_pn).map(|(p, &x, wt_n)| {
            repeat(-wt_n[4] * exp_iter(x).nth(self.m).unwrap()).take(p.mints.len())
        }));
        let scalars_M_k = (0..self.ring_size()).map(|k| {
            izip!(&mu_pk, &f_poly_pk, &wt_pn)
                .map(|(mu_k, f_poly_k, wt_n)| wt_n[2] * mu_k[k] * f_poly_k[k])
                .sum()
        });
        let scalars_P_k = (0..self.ring_size()).map(|k| {
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

#[derive(Clone)]
struct TensorIterator<'a, T> {
    tensor: &'a Vec<Vec<Vec<T>>>,
    w: usize,
    m: usize,
    n: usize,
    u: usize,
    j: usize,
    i: usize,
}

impl<'a, T> TensorIterator<'a, T> {
    fn new(tensor: &'a Vec<Vec<Vec<T>>>, w: usize, m: usize, n: usize) -> TensorIterator<'a, T> {
        let u = 0;
        let j = 0;
        let i = 0;
        TensorIterator {
            tensor,
            w,
            n,
            m,
            u,
            j,
            i,
        }
    }
}

impl<'a, T> Iterator for TensorIterator<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.u < self.w {
            let next = &self.tensor[self.u][self.j][self.i];
            self.i += 1;
            if self.i >= self.n {
                self.i = 0;
                self.j += 1;
            }
            if self.j >= self.m {
                self.j = 0;
                self.u += 1;
            }
            Some(next)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.w * self.m * self.n;
        (size, Some(size))
    }
}

/// Derive a generator point from some other base point, without a known logarithm.
/// A generator is derived by hashing 3 derivation indices (u, j, i) and the base point.
///
/// For example, to derive a new generator H_123 from base point G:
/// H_123 = hash(1 || 2 || 3 || G)
fn derive_generator(base: &RistrettoPoint, u: u32, j: u32, i: u32) -> RistrettoPoint {
    let mut bytes = [0u8; 4 + 4 + 4 + 32];
    bytes[0..4].copy_from_slice(&u.to_be_bytes());
    bytes[4..8].copy_from_slice(&j.to_be_bytes());
    bytes[8..12].copy_from_slice(&i.to_be_bytes());
    bytes[12..].copy_from_slice(base.compress().as_bytes());
    RistrettoPoint::hash_from_bytes::<Blake2b>(&bytes)
}

fn convert_base(num: usize, base: usize, digits: usize) -> Vec<usize> {
    let mut x_j = vec![0usize; digits];
    let mut x = num;
    let mut j = 0;
    while x > 0 {
        let q = x / base;
        x_j[j] = x - base * q;
        x = q;
        j += 1;
    }
    x_j
}

struct CycleTensorPolyEvals<'a> {
    w: usize,
    m: usize,
    n: usize,
    f_uji: &'a Vec<Vec<Vec<Scalar>>>,
    partial_digits_j: Vec<usize>,
    partial_prods_ju: Vec<Vec<Scalar>>,
}

fn cycle_tensor_poly_evals<'a>(f_uji: &'a Vec<Vec<Vec<Scalar>>>) -> CycleTensorPolyEvals<'a> {
    let w = f_uji.len();
    let m = f_uji[0].len();
    let n = f_uji[0][0].len();
    let partial_digits_j = Vec::with_capacity(m);
    let partial_prods_ju = vec![vec![Scalar::one(); w]; m];
    CycleTensorPolyEvals {
        w,
        m,
        n,
        f_uji,
        partial_digits_j,
        partial_prods_ju,
    }
}

impl CycleTensorPolyEvals<'_> {
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
        self.update();
        Some(self.partial_prods_ju.last().unwrap().iter().sum::<Scalar>())
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::max_value(), None)
    }
}

fn compute_p_j(k: usize, l: usize, a_ji: &Vec<Vec<Scalar>>) -> Vec<Scalar> {
    let m = a_ji.len();
    let n = a_ji[0].len();

    // Create polynomials for each n
    let mut p = Polynomial::from(Vec::with_capacity(m));
    p.push(Scalar::one());

    // Convert k & l to vectors of n-ary digits
    let k = convert_base(k, n, m);
    let l = convert_base(l, n, m);

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
    use crate::proof::*;
    use rand::rngs::OsRng; // You should use a more secure RNG

    #[test]
    fn new() {
        let gens = ArcturusGens::new(3, 2, 1).unwrap();
        assert_eq!(gens.n, 3);
        assert_eq!(gens.m, 2);
        assert_eq!(gens.w, 1);
        assert_eq!(
            ArcturusGens::new(1, 3, 3).unwrap_err(),
            ArcturusError::ProofRadixTooSmall
        );
        assert!(ArcturusGens::new(2, 3, 3).is_ok());
        assert!(ArcturusGens::new(32, 3, 3).is_ok());
        assert_eq!(
            ArcturusGens::new(3, 1, 3).unwrap_err(),
            ArcturusError::ProofDigitsTooSmall
        );
        assert!(ArcturusGens::new(3, 2, 3).is_ok());
        assert!(ArcturusGens::new(2, 32, 3).is_ok());
        assert_eq!(
            ArcturusGens::new(3, 3, 0).unwrap_err(),
            ArcturusError::ProofNumSignersTooSmall
        );
        assert!(ArcturusGens::new(3, 3, 1).is_ok());
        assert!(ArcturusGens::new(2, 6, 32).is_ok());
        assert!(ArcturusGens::new(2, 6, 33).is_ok());
        assert!(ArcturusGens::new(3, 3, 27).is_ok());
        assert_eq!(
            ArcturusGens::new(3, 3, 28).unwrap_err(),
            ArcturusError::ProofNumSignersTooLarge
        );
    }

    #[test]
    fn ring_size() {
        let gens = ArcturusGens::new(2, 2, 1).unwrap();
        assert_eq!(gens.ring_size(), 4);
        let gens = ArcturusGens::new(3, 2, 1).unwrap();
        assert_eq!(gens.ring_size(), 9);
        let gens = ArcturusGens::new(4, 4, 1).unwrap();
        assert_eq!(gens.ring_size(), 256);
    }

    #[test]
    fn commit() {
        let gens = ArcturusGens::new(2, 2, 1).unwrap();
        let A = gens.commit(&Scalar::from(100u32), &Scalar::from(10u32));
        let B = gens.commit(&Scalar::from(200u32), &Scalar::from(20u32));
        let C = gens.commit(&Scalar::from(300u32), &Scalar::from(30u32));
        assert_eq!(A + B, C);
    }

    #[test]
    fn prove_and_verify_5x2() {
        let gens = ArcturusGens::new(5, 2, 8).unwrap();

        // Build a random ring of outputs
        let mut ring = (0..gens.ring_size())
            .map(|_| {
                Output::new(
                    RistrettoPoint::random(&mut OsRng),
                    RistrettoPoint::random(&mut OsRng),
                )
            })
            .collect::<Vec<_>>();

        // Lets build our outputs
        let mut idxs_p = Vec::new();
        let mut spends_p = Vec::new();
        let mut mints_p = Vec::new();
        for p in 0..4 {
            let mut idxs = Vec::new();
            for i in 0..3 {
                idxs.push(p * 3 + i);
            }
            let mut spends = Vec::new();
            let mut mints = Vec::new();
            for &idx in &idxs {
                let privkey = Scalar::random(&mut OsRng);
                let pubkey = RistrettoPoint::random(&mut OsRng);
                let amount = 6600;
                let blind_spend = Scalar::random(&mut OsRng);
                let blind_mint = Scalar::random(&mut OsRng);
                let spend = SpendSecret::new(privkey, amount, blind_spend);
                let mint = MintSecret::new(pubkey, amount, blind_mint);
                ring[idx] = spend.to_output();
                spends.push(spend);
                mints.push(mint);
            }
            idxs_p.push(idxs);
            spends_p.push(spends);
            mints_p.push(mints);
        }

        let mut proofs = Vec::new();
        for (idxs, spends, mints) in izip!(&idxs_p, &spends_p, &mints_p) {
            let proof = gens
                .prove(
                    &mut Transcript::new(b"Arcturus-Test"),
                    &ring[..],
                    &idxs[..],
                    &spends[..],
                    &mints[..],
                )
                .unwrap();

            let mut t = Transcript::new(b"Arcturus-Test");
            assert!(gens
                .verify_batch(&mut t, &ring[..], &[proof.clone()])
                .is_ok());
            proofs.push(proof);
        }
        let mut t = Transcript::new(b"Arcturus-Test");
        assert!(gens.verify_batch(&mut t, &ring[..], &proofs[..]).is_ok());
    }

    #[test]
    fn prove_and_verify_2x5() {
        let gens = ArcturusGens::new(2, 5, 8).unwrap();

        // Build a random ring of outputs
        let mut ring = (0..gens.ring_size())
            .map(|_| {
                Output::new(
                    RistrettoPoint::random(&mut OsRng),
                    RistrettoPoint::random(&mut OsRng),
                )
            })
            .collect::<Vec<_>>();

        // Lets build our outputs
        let mut idxs_p = Vec::new();
        let mut spends_p = Vec::new();
        let mut mints_p = Vec::new();
        for p in 0..4 {
            let mut idxs = Vec::new();
            for i in 0..3 {
                idxs.push(p * 3 + i);
            }
            let mut spends = Vec::new();
            let mut mints = Vec::new();
            for &idx in &idxs {
                let privkey = Scalar::random(&mut OsRng);
                let pubkey = RistrettoPoint::random(&mut OsRng);
                let amount = 6600;
                let blind_spend = Scalar::random(&mut OsRng);
                let blind_mint = Scalar::random(&mut OsRng);
                let spend = SpendSecret::new(privkey, amount, blind_spend);
                let mint = MintSecret::new(pubkey, amount, blind_mint);
                ring[idx] = spend.to_output();
                spends.push(spend);
                mints.push(mint);
            }
            idxs_p.push(idxs);
            spends_p.push(spends);
            mints_p.push(mints);
        }

        let mut proofs = Vec::new();
        for (idxs, spends, mints) in izip!(&idxs_p, &spends_p, &mints_p) {
            let proof = gens
                .prove(
                    &mut Transcript::new(b"Arcturus-Test"),
                    &ring[..],
                    &idxs[..],
                    &spends[..],
                    &mints[..],
                )
                .unwrap();

            let mut t = Transcript::new(b"Arcturus-Test");
            assert!(gens.verify_batch(&mut t, &ring, &[proof.clone()]).is_ok());
            proofs.push(proof);
        }
        let mut t = Transcript::new(b"Arcturus-Test");
        assert!(gens.verify_batch(&mut t, &ring, &proofs[..]).is_ok());
    }

    #[test]
    fn proof_accessors() {
        let gens = ArcturusGens::new(2, 5, 8).unwrap();

        // Build a random ring of outputs
        let mut ring = (0..gens.ring_size())
            .map(|_| {
                Output::new(
                    RistrettoPoint::random(&mut OsRng),
                    RistrettoPoint::random(&mut OsRng),
                )
            })
            .collect::<Vec<_>>();

        // Lets build our outputs
        let mut idxs_p = Vec::new();
        let mut spends_p = Vec::new();
        let mut mints_p = Vec::new();
        for p in 0..4 {
            let mut idxs = Vec::new();
            for i in 0..3 {
                idxs.push(p * 3 + i);
            }
            let mut spends = Vec::new();
            let mut mints = Vec::new();
            for &idx in &idxs {
                let privkey = Scalar::random(&mut OsRng);
                let pubkey = RistrettoPoint::random(&mut OsRng);
                let amount = 6600;
                let blind_spend = Scalar::random(&mut OsRng);
                let blind_mint = Scalar::random(&mut OsRng);
                let spend = SpendSecret::new(privkey, amount, blind_spend);
                let mint = MintSecret::new(pubkey, amount, blind_mint);
                ring[idx] = spend.to_output();
                spends.push(spend);
                mints.push(mint);
            }
            idxs_p.push(idxs);
            spends_p.push(spends);
            mints_p.push(mints);
        }

        for (idxs, spends, mints) in izip!(&idxs_p, &spends_p, &mints_p) {
            let proof = gens
                .prove(
                    &mut Transcript::new(b"Arcturus-Test"),
                    &ring[..],
                    &idxs[..],
                    &spends[..],
                    &mints[..],
                )
                .unwrap();
            assert_eq!(proof.count_spends(), spends.len());
            assert_eq!(proof.count_mints(), mints.len());
            for (i, tag) in proof.spend_tags().iter().enumerate() {
                assert_eq!(tag, &spends[i].get_tag());
            }
            for (i, mint) in proof.mints().iter().enumerate() {
                assert_eq!(mint, &mints[i].to_output());
            }
        }
    }

    #[test]
    fn prove_errors() {
        let gens = ArcturusGens::new(2, 5, 8).unwrap();

        // Build a random ring of outputs
        let mut ring = (0..gens.ring_size())
            .map(|_| {
                Output::new(
                    RistrettoPoint::random(&mut OsRng),
                    RistrettoPoint::random(&mut OsRng),
                )
            })
            .collect::<Vec<_>>();

        // Lets build our outputs
        let mut idxs = Vec::new();
        for i in 0..3 {
            idxs.push(i);
        }
        let mut spends = Vec::new();
        let mut mints = Vec::new();
        for &idx in &idxs {
            let privkey = Scalar::random(&mut OsRng);
            let pubkey = RistrettoPoint::random(&mut OsRng);
            let amount = 6600;
            let blind_spend = Scalar::random(&mut OsRng);
            let blind_mint = Scalar::random(&mut OsRng);
            let spend = SpendSecret::new(privkey, amount, blind_spend);
            let mint = MintSecret::new(pubkey, amount, blind_mint);
            ring[idx] = spend.to_output();
            spends.push(spend);
            mints.push(mint);
        }

        // First make sure the proof succeeds
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_ok());

        // Now remove a spend, so that the mints and spends no longer balance.
        spends.pop();
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_err());
    }
}
