#![allow(non_snake_case)]
use crate::generators::derive_generator;
use blake2::Blake2b;
use curve25519_dalek::constants;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// An output consists of a public key and a Pedersen commitment.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Output {
    pub(crate) pubkey: RistrettoPoint,
    pub(crate) commit: RistrettoPoint,
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
    pub(crate) privkey: Scalar,
    pub(crate) amount: Scalar,
    pub(crate) blind: Scalar,
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
    pub(crate) pubkey: RistrettoPoint,
    pub(crate) amount: Scalar,
    pub(crate) blind: Scalar,
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

#[cfg(test)]
mod tests {
    use super::*;
    use curve25519_dalek::ristretto::CompressedRistretto;

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
}
