#![allow(non_snake_case)]
use crate::errors::{ArcturusError, ArcturusResult};
use crate::transcript::TranscriptProtocol;
use crate::util::{exp_iter, sized_flatten, RadixDecomposer};
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

    pub fn output(&self) -> Output {
        let G = constants::RISTRETTO_BASEPOINT_POINT;
        let H = derive_generator(&G, 0, 0, 0);
        let pubkey = self.privkey * G;
        let commit = self.amount * H + self.blind * G;
        Output { pubkey, commit }
    }

    pub fn tag(&self) -> RistrettoPoint {
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

    pub fn output(&self) -> Output {
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

    pub fn tags(&self) -> &Vec<RistrettoPoint> {
        &self.J_u
    }

    pub fn mints(&self) -> &Vec<Output> {
        &self.mints
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
        } else if idxs.len() > self.w {
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
            once(&rA).chain(flatten_3d!(&a_uji[0..u])),
            once(&self.G).chain(flatten_3d!(&self.H_uji[0..u])),
        );

        // Convert each index from binary to a `m` digit `n-ary` number
        let sigma_uji = idxs
            .iter()
            .map(|&l| {
                RadixDecomposer::new(l, self.n)
                    .take(self.m)
                    .map(|l_j| {
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
            once(&rB).chain(flatten_3d!(&sigma_uji[0..u])),
            once(&self.G).chain(flatten_3d!(&self.H_uji[0..u])),
        );

        // C = Com(a*(1-2*sigma), rC) = rB*G + (a_uji*(1-2*sigma_uji))*H_uji
        let C_vals_uji = izip!(flatten_3d!(&sigma_uji[0..u]), flatten_3d!(&a_uji[0..u]))
            .map(|(sigma, a)| a * (Scalar::one() - Scalar::from(2u32) * sigma));
        let rC = Scalar::random(&mut rng);
        let C = RistrettoPoint::multiscalar_mul(
            once(rC).chain(C_vals_uji),
            once(&self.G).chain(flatten_3d!(&self.H_uji[0..u])),
        );

        // D = Com(-a^2, rD) = rD*G + -a_uji*a_uji*H_uji
        let rD = Scalar::random(&mut rng);
        let D = RistrettoPoint::multiscalar_mul(
            once(rD).chain(flatten_3d!(&a_uji[0..u]).map(|a| -a * a)),
            once(&self.G).chain(flatten_3d!(&self.H_uji[0..u])),
        );

        // Generate randomness rho & rhobar
        let rho_uj = (0..u)
            .map(|_| (0..self.m).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();
        let rhobar_uj = (0..u)
            .map(|_| (0..self.m).map(|_| Scalar::random(&mut rng)).collect())
            .collect::<Vec<Vec<_>>>();

        // Compute spend tags
        let J_u = spends.iter().map(|s| s.tag()).collect::<Vec<_>>();

        // Compute minted outputs
        let mints_pub = mints.iter().map(|m| m.output()).collect::<Vec<_>>();

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
                CycleTensorPolyEvals::new(&f_uji, 0)
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
        let points_H_uji = flatten_3d!(&self.H_uji[0..u_max]);
        let points_A_p = proofs.iter().map(|p| &p.A);
        let points_B_p = proofs.iter().map(|p| &p.B);
        let points_C_p = proofs.iter().map(|p| &p.C);
        let points_D_p = proofs.iter().map(|p| &p.D);
        let points_X_pj = sized_flatten(proofs.iter().map(|p| p.X_j.iter()));
        let points_Y_pj = sized_flatten(proofs.iter().map(|p| p.Y_j.iter()));
        let points_Z_pj = sized_flatten(proofs.iter().map(|p| p.Z_j.iter()));
        let points_J_pu = sized_flatten(proofs.iter().map(|p| p.J_u.iter()));
        let points_Q_pt = sized_flatten(proofs.iter().map(|p| p.mints.iter().map(|O| &O.commit)));
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
        let scalars_X_pj = sized_flatten(
            izip!(&x_p, &wt_pn)
                .map(|(&x, wt_n)| exp_iter(x).take(self.m).map(move |xj| -wt_n[2] * xj)),
        );
        let scalars_Y_pj = sized_flatten(
            izip!(&x_p, &wt_pn)
                .map(|(&x, wt_n)| exp_iter(x).take(self.m).map(move |xj| -wt_n[3] * xj)),
        );
        let scalars_Z_pj = sized_flatten(
            izip!(&x_p, &wt_pn)
                .map(|(&x, wt_n)| exp_iter(x).take(self.m).map(move |xj| -wt_n[4] * xj)),
        );
        let scalars_J_pu = sized_flatten(
            izip!(proofs, &wt_pn).map(|(p, wt_n)| p.zR_u.iter().map(move |zR| -wt_n[3] * zR)),
        );
        let scalars_Q_pt = sized_flatten(izip!(proofs, &x_p, &wt_pn).map(|(p, &x, wt_n)| {
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
    use curve25519_dalek::ristretto::CompressedRistretto;
    use rand::rngs::OsRng; // You should use a more secure RNG

    const G: RistrettoPoint = constants::RISTRETTO_BASEPOINT_POINT;
    const H: CompressedRistretto = CompressedRistretto([
        88, 20, 136, 75, 248, 210, 190, 177, 173, 233, 152, 155, 220, 94, 58, 58, 119, 94, 58, 212,
        93, 51, 131, 1, 105, 167, 53, 130, 234, 250, 194, 116,
    ]);
    const U: CompressedRistretto = CompressedRistretto([
        198, 215, 127, 137, 59, 90, 1, 165, 233, 149, 190, 90, 86, 142, 85, 187, 34, 243, 147, 30,
        230, 134, 242, 78, 93, 33, 27, 238, 150, 126, 198, 109,
    ]);

    #[test]
    fn output_new() {
        let mut rng = rand::thread_rng();
        let pubkey = RistrettoPoint::random(&mut rng);
        let commit = RistrettoPoint::random(&mut rng);
        let O = Output::new(pubkey, commit);
        assert_eq!(pubkey, O.pubkey);
        assert_eq!(commit, O.commit);
    }

    struct SpendSecretTest {
        privkey_bytes: [u8; 32],
        amount: u64,
        blind_bytes: [u8; 32],
        output_pubkey: CompressedRistretto,
        output_commit: CompressedRistretto,
        tag: CompressedRistretto,
    }
    const SPEND_SECRET_TESTS: [SpendSecretTest; 3] = [
        SpendSecretTest {
            privkey_bytes: [
                199, 49, 149, 210, 237, 208, 113, 146, 229, 119, 140, 101, 71, 221, 7, 57, 192,
                167, 27, 81, 96, 93, 227, 46, 52, 113, 106, 48, 108, 215, 89, 5,
            ],
            amount: 9351062461309522351,
            blind_bytes: [
                51, 102, 48, 203, 162, 146, 42, 217, 85, 174, 55, 26, 2, 241, 18, 49, 130, 224, 61,
                241, 175, 14, 186, 90, 31, 48, 63, 54, 208, 9, 54, 7,
            ],
            output_pubkey: CompressedRistretto([
                106, 68, 82, 198, 54, 61, 203, 175, 140, 87, 223, 195, 153, 105, 142, 131, 234,
                235, 94, 92, 2, 111, 161, 121, 63, 24, 117, 56, 115, 220, 90, 42,
            ]),
            output_commit: CompressedRistretto([
                248, 19, 97, 81, 254, 71, 179, 41, 172, 142, 79, 91, 19, 187, 213, 14, 155, 228,
                197, 105, 14, 219, 17, 184, 37, 82, 244, 252, 235, 253, 168, 43,
            ]),
            tag: CompressedRistretto([
                224, 120, 26, 30, 161, 71, 24, 221, 142, 36, 244, 207, 142, 99, 127, 139, 7, 25,
                207, 182, 0, 48, 3, 25, 96, 226, 150, 174, 93, 117, 11, 60,
            ]),
        },
        SpendSecretTest {
            privkey_bytes: [
                59, 221, 78, 25, 134, 165, 2, 25, 75, 12, 33, 169, 176, 110, 35, 149, 150, 96, 48,
                248, 246, 228, 168, 81, 199, 157, 196, 81, 106, 0, 218, 4,
            ],
            amount: 17228059461709348854,
            blind_bytes: [
                243, 92, 3, 227, 23, 136, 147, 135, 11, 131, 250, 56, 157, 224, 181, 245, 245, 17,
                33, 87, 94, 1, 37, 61, 46, 10, 91, 80, 80, 22, 237, 3,
            ],
            output_pubkey: CompressedRistretto([
                134, 150, 244, 210, 225, 207, 126, 163, 172, 65, 0, 85, 155, 100, 90, 39, 119, 125,
                223, 74, 68, 10, 73, 34, 123, 176, 179, 26, 92, 117, 175, 98,
            ]),
            output_commit: CompressedRistretto([
                48, 195, 75, 120, 80, 23, 72, 56, 46, 147, 171, 99, 196, 236, 212, 252, 53, 38,
                201, 194, 220, 8, 46, 73, 123, 144, 133, 245, 56, 70, 33, 16,
            ]),
            tag: CompressedRistretto([
                132, 44, 143, 68, 212, 174, 73, 121, 148, 159, 165, 136, 61, 215, 38, 221, 198,
                214, 233, 189, 149, 138, 225, 215, 236, 184, 102, 97, 84, 244, 249, 112,
            ]),
        },
        SpendSecretTest {
            privkey_bytes: [
                193, 220, 228, 127, 249, 213, 40, 253, 151, 135, 102, 3, 35, 133, 15, 203, 212,
                208, 65, 179, 204, 68, 211, 121, 251, 214, 110, 5, 29, 213, 171, 9,
            ],
            amount: 1865828838350312698,
            blind_bytes: [
                177, 115, 105, 217, 47, 207, 175, 228, 86, 29, 52, 219, 120, 93, 210, 10, 134, 180,
                130, 246, 79, 63, 70, 243, 243, 112, 63, 232, 54, 55, 236, 12,
            ],
            output_pubkey: CompressedRistretto([
                72, 209, 22, 128, 103, 48, 98, 140, 77, 64, 201, 152, 217, 104, 133, 36, 150, 93,
                218, 69, 3, 92, 7, 25, 52, 142, 222, 241, 220, 218, 127, 2,
            ]),
            output_commit: CompressedRistretto([
                76, 96, 211, 192, 179, 169, 6, 39, 142, 108, 149, 86, 56, 7, 93, 13, 228, 174, 156,
                136, 156, 244, 184, 34, 84, 144, 165, 193, 217, 198, 70, 14,
            ]),
            tag: CompressedRistretto([
                68, 234, 247, 30, 128, 78, 125, 77, 151, 14, 219, 30, 14, 24, 218, 216, 173, 194,
                214, 12, 11, 95, 164, 234, 226, 188, 37, 67, 74, 192, 11, 64,
            ]),
        },
    ];

    #[test]
    fn spend_secret_new() {
        let mut rng = rand::thread_rng();
        let privkey = Scalar::random(&mut rng);
        let blind = Scalar::random(&mut rng);
        let amount: u64 = rand::random();
        let ss = SpendSecret::new(privkey, amount, blind);
        assert_eq!(privkey, ss.privkey);
        assert_eq!(Scalar::from(amount), ss.amount);
        assert_eq!(blind, ss.blind);
    }

    #[test]
    fn spend_secret_output() {
        let mut rng = rand::thread_rng();

        // Test against some random cases
        for _ in 0..4 {
            let privkey = Scalar::random(&mut rng);
            let blind = Scalar::random(&mut rng);
            let amount: u64 = rand::random();
            let pubkey = privkey * G;
            let commit = Scalar::from(amount) * H.decompress().unwrap() + blind * G;
            let O = SpendSecret::new(privkey, amount, blind).output();
            assert_eq!(pubkey, O.pubkey);
            assert_eq!(commit, O.commit);
        }

        // Test against some hard-coded cases
        for test in &SPEND_SECRET_TESTS {
            let privkey = Scalar::from_bytes_mod_order(test.privkey_bytes);
            let blind = Scalar::from_bytes_mod_order(test.blind_bytes);
            let pubkey = privkey * G;
            let commit = Scalar::from(test.amount) * H.decompress().unwrap() + blind * G;
            let O = SpendSecret::new(privkey, test.amount, blind).output();
            assert_eq!(test.output_pubkey, pubkey.compress());
            assert_eq!(test.output_pubkey, O.pubkey.compress());
            assert_eq!(test.output_commit, commit.compress());
            assert_eq!(test.output_commit, O.commit.compress());
        }
    }

    #[test]
    fn spend_secret_tag() {
        let mut rng = rand::thread_rng();

        // Test against some random cases
        for _ in 0..4 {
            let privkey = Scalar::random(&mut rng);
            let blind = Scalar::random(&mut rng);
            let amount: u64 = rand::random();
            let ss = SpendSecret::new(privkey, amount, blind);
            let tag = ss.tag();
            assert_eq!(tag, privkey.invert() * U.decompress().unwrap());
        }

        // Test against some hard-coded cases
        for test in &SPEND_SECRET_TESTS {
            let privkey = Scalar::from_bytes_mod_order(test.privkey_bytes);
            let blind = Scalar::from_bytes_mod_order(test.blind_bytes);
            let ss = SpendSecret::new(privkey, test.amount, blind);
            let tag = ss.tag();
            assert_eq!(test.tag, tag.compress());
            assert_eq!(tag, privkey.invert() * U.decompress().unwrap());
        }
    }

    struct MintSecretTest {
        pubkey: CompressedRistretto,
        amount: u64,
        blind_bytes: [u8; 32],
        output_pubkey: CompressedRistretto,
        output_commit: CompressedRistretto,
    }
    const MINT_SECRET_TESTS: [MintSecretTest; 2] = [
        MintSecretTest {
            pubkey: CompressedRistretto([
                26, 180, 76, 213, 19, 22, 162, 69, 60, 240, 54, 0, 85, 11, 248, 132, 173, 38, 10,
                90, 122, 224, 11, 52, 140, 155, 139, 124, 0, 216, 125, 99,
            ]),
            amount: 3762547364937691008,
            blind_bytes: [
                231, 232, 180, 230, 197, 129, 36, 213, 178, 125, 90, 187, 183, 66, 63, 106, 123,
                78, 145, 202, 181, 206, 194, 92, 170, 112, 210, 228, 26, 148, 47, 12,
            ],
            output_pubkey: CompressedRistretto([
                26, 180, 76, 213, 19, 22, 162, 69, 60, 240, 54, 0, 85, 11, 248, 132, 173, 38, 10,
                90, 122, 224, 11, 52, 140, 155, 139, 124, 0, 216, 125, 99,
            ]),
            output_commit: CompressedRistretto([
                164, 139, 233, 64, 44, 43, 62, 12, 203, 157, 40, 25, 173, 70, 120, 126, 155, 200,
                69, 77, 135, 224, 43, 6, 151, 28, 99, 5, 123, 241, 59, 8,
            ]),
        },
        MintSecretTest {
            pubkey: CompressedRistretto([
                252, 184, 136, 4, 72, 247, 191, 166, 246, 20, 105, 149, 95, 28, 85, 107, 117, 36,
                122, 229, 29, 134, 201, 65, 122, 137, 194, 168, 12, 73, 115, 73,
            ]),
            amount: 15455118957639524404,
            blind_bytes: [
                53, 195, 30, 103, 129, 253, 249, 179, 60, 94, 58, 247, 111, 19, 245, 72, 244, 40,
                54, 63, 178, 215, 211, 2, 7, 192, 198, 27, 168, 119, 228, 9,
            ],
            output_pubkey: CompressedRistretto([
                252, 184, 136, 4, 72, 247, 191, 166, 246, 20, 105, 149, 95, 28, 85, 107, 117, 36,
                122, 229, 29, 134, 201, 65, 122, 137, 194, 168, 12, 73, 115, 73,
            ]),
            output_commit: CompressedRistretto([
                224, 252, 68, 165, 233, 145, 236, 149, 109, 96, 35, 1, 56, 123, 100, 221, 131, 216,
                118, 5, 0, 255, 90, 120, 100, 67, 35, 215, 34, 254, 236, 115,
            ]),
        },
    ];

    #[test]
    fn mint_secret_new() {
        let mut rng = rand::thread_rng();

        // Test against some random cases
        for _ in 0..4 {
            let pubkey = RistrettoPoint::random(&mut rng);
            let amount: u64 = rand::random();
            let blind = Scalar::random(&mut rng);
            let ms = MintSecret::new(pubkey, amount, blind);
            assert_eq!(pubkey, ms.pubkey);
            assert_eq!(Scalar::from(amount), ms.amount);
            assert_eq!(blind, ms.blind);
        }

        // Test against some hard-coded cases
        for test in &MINT_SECRET_TESTS {
            let pubkey = test.pubkey.decompress().unwrap();
            let blind = Scalar::from_bytes_mod_order(test.blind_bytes);
            let ms = MintSecret::new(pubkey, test.amount, blind);
            assert_eq!(test.pubkey, ms.pubkey.compress());
            assert_eq!(Scalar::from(test.amount), ms.amount);
            assert_eq!(blind, ms.blind);
        }
    }

    #[test]
    fn mint_secret_output() {
        let mut rng = rand::thread_rng();

        // Test against some random cases
        for _ in 0..4 {
            let pubkey = RistrettoPoint::random(&mut rng);
            let amount: u64 = rand::random();
            let blind = Scalar::random(&mut rng);
            let commit = Scalar::from(amount) * H.decompress().unwrap() + blind * G;
            let O = MintSecret::new(pubkey, amount, blind).output();
            assert_eq!(pubkey, O.pubkey);
            assert_eq!(commit, O.commit);
        }

        // Test against some hard-coded cases
        for test in &MINT_SECRET_TESTS {
            let pubkey = test.pubkey.decompress().unwrap();
            let blind = Scalar::from_bytes_mod_order(test.blind_bytes);
            let commit = Scalar::from(test.amount) * H.decompress().unwrap() + blind * G;
            let O = MintSecret::new(pubkey, test.amount, blind).output();
            assert_eq!(test.output_pubkey, pubkey.compress());
            assert_eq!(test.output_pubkey, O.pubkey.compress());
            assert_eq!(test.output_commit, commit.compress());
            assert_eq!(test.output_commit, O.commit.compress());
        }
    }

    #[test]
    fn arcturus_proof() {
        let gens = ArcturusGens::new(2, 5, 8).unwrap();

        // Build a ring of random outputs
        let mut ring = (0..gens.ring_size())
            .map(|_| {
                Output::new(
                    RistrettoPoint::random(&mut OsRng),
                    RistrettoPoint::random(&mut OsRng),
                )
            })
            .collect::<Vec<_>>();
        assert!(ring.len() > 2);

        // Inject known outputs into the ring, which we can use to sign a proof
        // Known outputs should just be injected at arbitrary indices.
        let idxs = (2..7).collect::<Vec<usize>>();
        let mut spends = Vec::new();
        let mut mints = Vec::new();
        for &idx in idxs.iter() {
            let privkey = Scalar::random(&mut OsRng);
            let pubkey = RistrettoPoint::random(&mut OsRng);
            let amount = 6600;
            let blind_spend = Scalar::random(&mut OsRng);
            let blind_mint = Scalar::random(&mut OsRng);
            let spend = SpendSecret::new(privkey, amount, blind_spend);
            let mint = MintSecret::new(pubkey, amount, blind_mint);
            ring[idx] = spend.output();
            spends.push(spend);
            mints.push(mint);
        }

        // Build the proof
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
        for (tag, spend) in izip!(proof.tags().clone(), &spends) {
            assert_eq!(tag, spend.tag());
        }
        for (i, mint) in proof.mints().iter().enumerate() {
            assert_eq!(mint, &mints[i].output());
        }
    }

    #[test]
    fn arcturus_gens_new() {
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
    fn arcturus_gens_ring_size() {
        let gens = ArcturusGens::new(2, 2, 1).unwrap();
        assert_eq!(gens.ring_size(), 4);
        let gens = ArcturusGens::new(3, 2, 1).unwrap();
        assert_eq!(gens.ring_size(), 9);
        let gens = ArcturusGens::new(4, 4, 1).unwrap();
        assert_eq!(gens.ring_size(), 256);
    }

    #[test]
    fn arcturus_gens_commit() {
        let gens = ArcturusGens::new(2, 2, 1).unwrap();
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
                ring[idx] = spend.output();
                spends.push(spend);
                mints.push(mint);
            }
            idxs_p.push(idxs);
            spends_p.push(spends);
            mints_p.push(mints);
        }

        // Test prooving and verifying individual proofs
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

        // Test batch verification
        let mut t = Transcript::new(b"Arcturus-Test");
        assert!(gens.verify_batch(&mut t, &ring[..], &proofs[..]).is_ok());

        // Build a proof with too many witnesses, and confirm error
        let mut idxs = Vec::new();
        for i in 0..9 {
            // One more than max witnesses
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
            ring[idx] = spend.output();
            spends.push(spend);
            mints.push(mint);
        }
        // Should error: too many witnesses
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_err());

        idxs.pop();
        // Should error: idx.len() != spends.len()
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_err());

        spends.pop();
        // Should error: mints and spends don't balance
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_err());

        mints.pop();
        // Should succeed
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_ok());
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
                ring[idx] = spend.output();
                spends.push(spend);
                mints.push(mint);
            }
            idxs_p.push(idxs);
            spends_p.push(spends);
            mints_p.push(mints);
        }

        // Test prooving and verifying individual proofs
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

        // Test batch verification
        let mut t = Transcript::new(b"Arcturus-Test");
        assert!(gens.verify_batch(&mut t, &ring, &proofs[..]).is_ok());

        // Build a proof with too many witnesses, and confirm error
        let mut idxs = Vec::new();
        for i in 0..9 {
            // One more than max witnesses
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
            ring[idx] = spend.output();
            spends.push(spend);
            mints.push(mint);
        }
        // Should error: too many witnesses
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_err());

        idxs.pop();
        // Should error: idx.len() != spends.len()
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_err());

        spends.pop();
        // Should error: mints and spends don't balance
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_err());

        mints.pop();
        // Should succeed
        assert!(gens
            .prove(
                &mut Transcript::new(b"Arcturus-Test"),
                &ring[..],
                &idxs[..],
                &spends[..],
                &mints[..],
            )
            .is_ok());
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
            ring[idx] = spend.output();
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
