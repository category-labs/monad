// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

//! Host tests of the guest's secp256k1 recovery (../src/ecrecover.rs)
//! against k256. ziskos emulates the ZisK precompiles and hints on the host;
//! its inversion modulo n calls ZisK's C library, which ziskos builds on
//! Linux only, so the tests run there.

#[path = "../../src/ecrecover.rs"]
mod ecrecover;
#[path = "../../src/ecrecover_tables.rs"]
mod ecrecover_tables;

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::ecrecover::monad_zkvm_secp256k1_recover;
    use super::ecrecover_tables::G_JOINT;
    use k256::ecdsa::{RecoveryId, Signature, SigningKey, VerifyingKey};
    use k256::elliptic_curve::ops::Reduce;
    use k256::elliptic_curve::point::DecompressPoint;
    use k256::elliptic_curve::sec1::ToEncodedPoint;
    use k256::elliptic_curve::subtle::Choice;
    use k256::elliptic_curve::PrimeField;
    use k256::{AffinePoint, FieldBytes, ProjectivePoint, Scalar, U256};
    use std::sync::Mutex;

    /// The recovery keeps its state in statics: one call at a time.
    static RECOVERY_LOCK: Mutex<()> = Mutex::new(());

    /// The group order n, little-endian limbs.
    const N: [u64; 4] = [
        0xBFD25E8CD0364141,
        0xBAAEDCE6AF48A03B,
        0xFFFFFFFFFFFFFFFE,
        0xFFFFFFFFFFFFFFFF,
    ];

    /// xorshift64, fixed seed: failures are reproducible.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn limbs(&mut self) -> [u64; 4] {
            [self.next(), self.next(), self.next(), self.next()]
        }
    }

    fn be_bytes(limbs: &[u64; 4]) -> FieldBytes {
        let mut bytes = [0u8; 32];
        for i in 0..4 {
            bytes[8 * i..8 * i + 8].copy_from_slice(&limbs[3 - i].to_be_bytes());
        }
        FieldBytes::from(bytes)
    }

    fn be_to_limbs(bytes: &[u8]) -> [u64; 4] {
        let mut limbs = [0u64; 4];
        for i in 0..4 {
            limbs[3 - i] = u64::from_be_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap());
        }
        limbs
    }

    fn scalar_limbs(scalar: &Scalar) -> [u64; 4] {
        be_to_limbs(&scalar.to_bytes())
    }

    /// The guest's output: x then y, big-endian bytes, in eight words.
    fn output_words(point: &AffinePoint) -> [u64; 8] {
        let encoded = point.to_encoded_point(false);
        let mut words = [0u64; 8];
        for (j, word) in words.iter_mut().enumerate() {
            *word =
                u64::from_ne_bytes(encoded.as_bytes()[1 + 8 * j..9 + 8 * j].try_into().unwrap());
        }
        words
    }

    /// k256 under the guest's rules: r and s in [1, n), recid 0 or 1, R the
    /// point with x = r and y of parity recid, Q = r⁻¹·(s·R − z·G), and no
    /// key at infinity.
    fn reference(z: &[u64; 4], r: &[u64; 4], s: &[u64; 4], recid: u8) -> Option<[u64; 8]> {
        if recid > 1 {
            return None;
        }
        let r_scalar = Option::<Scalar>::from(Scalar::from_repr(be_bytes(r)))?;
        let s_scalar = Option::<Scalar>::from(Scalar::from_repr(be_bytes(s)))?;
        if bool::from(r_scalar.is_zero()) || bool::from(s_scalar.is_zero()) {
            return None;
        }
        let r_point = Option::<AffinePoint>::from(AffinePoint::decompress(
            &be_bytes(r),
            Choice::from(recid),
        ))?;
        let z_scalar = <Scalar as Reduce<U256>>::reduce_bytes(&be_bytes(z));
        let r_inverse = r_scalar.invert().unwrap();
        let q = ProjectivePoint::from(r_point) * (s_scalar * r_inverse)
            - ProjectivePoint::GENERATOR * (z_scalar * r_inverse);
        if q == ProjectivePoint::IDENTITY {
            return None;
        }
        Some(output_words(&q.to_affine()))
    }

    fn recover(z: &[u64; 4], r: &[u64; 4], s: &[u64; 4], recid: u8) -> Option<[u64; 8]> {
        let _guard = RECOVERY_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let mut out = [0u64; 8];
        let recovered = unsafe { monad_zkvm_secp256k1_recover(z, r, s, recid, &mut out) };
        recovered.then_some(out)
    }

    /// Compare with k256; return whether a key was recovered.
    fn check(z: &[u64; 4], r: &[u64; 4], s: &[u64; 4], recid: u8) -> bool {
        let expected = reference(z, r, s, recid);
        assert_eq!(
            recover(z, r, s, recid),
            expected,
            "z={z:x?} r={r:x?} s={s:x?} recid={recid}"
        );
        expected.is_some()
    }

    #[test]
    fn signatures_from_k256() {
        let mut rng = Rng(0x9E3779B97F4A7C15);
        let mut signed = 0;
        while signed < 1000 {
            let mut key = [0u8; 32];
            for chunk in key.chunks_mut(8) {
                chunk.copy_from_slice(&rng.next().to_be_bytes());
            }
            let Ok(signing_key) = SigningKey::from_bytes((&key).into()) else {
                continue;
            };
            let mut digest = [0u8; 32];
            for chunk in digest.chunks_mut(8) {
                chunk.copy_from_slice(&rng.next().to_be_bytes());
            }
            let (signature, recovery_id): (Signature, RecoveryId) =
                signing_key.sign_prehash_recoverable(&digest).unwrap();
            let signature = signature.to_bytes();
            let (z, r, s) = (
                be_to_limbs(&digest),
                be_to_limbs(&signature[..32]),
                be_to_limbs(&signature[32..]),
            );
            let expected = output_words(VerifyingKey::from(&signing_key).as_affine());
            assert_eq!(recover(&z, &r, &s, recovery_id.to_byte()), Some(expected));
            signed += 1;
        }
    }

    /// Random inputs, some out of range: r ≥ n, s = 0, recid up to 4, and r
    /// with no curve point (the non-residue rejection).
    #[test]
    fn random_inputs() {
        let mut rng = Rng(0xD1B54A32D192ED03);
        let (mut recovered, mut rejected) = (0, 0);
        for _ in 0..2000 {
            let z = rng.limbs();
            let mut r = rng.limbs();
            let mut s = rng.limbs();
            if rng.next() % 16 == 0 {
                r[3] = u64::MAX;
            }
            if rng.next() % 32 == 0 {
                s = [0; 4];
            }
            if rng.next() % 32 == 0 {
                r = N;
            }
            let recid = (rng.next() % 5) as u8;
            if check(&z, &r, &s, recid) {
                recovered += 1;
            } else {
                rejected += 1;
            }
        }
        assert!(
            recovered > 0 && rejected > 0,
            "{recovered} recovered, {rejected} rejected"
        );
    }

    /// R a small multiple of G or of 2^128·G (the table's rows), with z in
    /// {0, n, 2^256 − 1, s, 1, random}: u1 = 0, z ≥ n, and R sharing x with
    /// the generator's window points.
    #[test]
    fn edge_scalars() {
        let mut rng = Rng(0x2545F4914F6CDD1D);
        for rows in [false, true] {
            for k in 0..255usize {
                let row = if rows { 64 * (k % 63 + 1) - 1 } else { k };
                let r = G_JOINT[row].x;
                let s_values = [
                    [1u64, 0, 0, 0],
                    [2, 0, 0, 0],
                    [k as u64 + 1, 0, 0, 0],
                    rng.limbs(),
                    [N[0] - 1, N[1], N[2], N[3]],
                ];
                for s in s_values {
                    for z in [[0u64; 4], N, [u64::MAX; 4], s, [1, 0, 0, 0], rng.limbs()] {
                        for recid in 0..2 {
                            check(&z, &r, &s, recid);
                        }
                    }
                }
            }
        }
    }

    /// R = ±m·G or ±m·2^128·G with small u1 and u2 (z = −u1·r, s = u2·r): the
    /// accumulator meets points of equal x, both equal (a doubling) and
    /// opposite (a cancellation), and Q is at infinity when u1 = ±u2·m.
    #[test]
    fn crafted_cancellations() {
        for rows in [false, true] {
            for k in 0..20usize {
                let r = G_JOINT[if rows { 64 * (k + 1) - 1 } else { k }].x;
                let r_scalar = Scalar::from_repr(be_bytes(&r)).unwrap();
                for recid in 0..2u8 {
                    for u1 in (0..40u64)
                        .chain(256..270)
                        .chain(4096..4100)
                        .chain(65536..65546)
                    {
                        for u2 in [1u64, 2, 3, 15, 16, 17, 31, 255, 256, 257, 4097] {
                            let z = scalar_limbs(&(-(Scalar::from(u1) * r_scalar)));
                            let s = scalar_limbs(&(Scalar::from(u2) * r_scalar));
                            check(&z, &r, &s, recid);
                        }
                    }
                }
            }
        }
    }
}
