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

//! The 19 eth-act accelerators (zkvm/core/zkvm_accelerators.h) on OpenVM.
//!
//! On ZisK these come from ziskos, on SP1 from libzkevm.a; OpenVM has no
//! eth-act accelerator library, so this crate implements the whole surface
//! over OpenVM's guest extension crates. Where no extension exists the
//! fallback is software over whatever *is* accelerated: ripemd160, blake2f and
//! arbitrary-modulus modexp are pure software, while the BLS12-381
//! map-to-curve (`bls12_map`) and KZG point evaluation are built on the
//! accelerated field and pairing operations.
//!
//! Conventions follow the header (and thus ZisK): ripemd160 digest at bytes
//! [12,32) with a zero prefix, EIP-2537 byte encodings for BLS12-381 points
//! (big-endian field elements, all-zero = point at infinity, Fp2 = c0 || c1).
//! precompiles_impl.hpp therefore needs no per-backend branch for OpenVM, and
//! defines no `MONAD_ZKVM_OPENVM` — the golden vectors confirm it.
//!
//! Validated by the precompile golden-vector guest
//! (zkvm/test/precompile_tests): 1961/1961, the 1847-case go-ethereum set plus
//! the 114 KZG cases its `--kzg` flag adds.

use alloc::vec::Vec;

use openvm_algebra_guest::{IntMod, Sqrt};
use openvm_ecc_guest::{weierstrass::WeierstrassPoint, AffinePoint, Group};
use openvm_pairing::bls12_381::{
    Bls12_381, Fp as BlsFp, Fp2 as BlsFp2, G1Affine as BlsG1, G2Affine as BlsG2,
    Scalar as BlsScalar,
};
use openvm_pairing::bn254::{
    Bn254, Fp as Bn254Fp, Fp2 as Bn254Fp2, G1Affine as Bn254G1,
    G2Affine as Bn254G2, Scalar as Bn254Scalar,
};
use openvm_pairing::PairingCheck;
use ripemd::Digest as _;

pub const ZKVM_EOK: i32 = 0;
pub const ZKVM_EFAIL: i32 = -1;

// Byte-array types mirroring zkvm_accelerators.h (all 8-byte aligned).
macro_rules! bytes_type {
    ($name:ident, $len:expr) => {
        #[repr(C, align(8))]
        pub struct $name {
            pub data: [u8; $len],
        }
    };
}

bytes_type!(Bytes16, 16);
bytes_type!(Bytes32, 32);
bytes_type!(Bytes48, 48);
bytes_type!(Bytes64, 64);
bytes_type!(Bytes96, 96);
bytes_type!(Bytes128, 128);
bytes_type!(Bytes192, 192);

#[repr(C)]
pub struct Bn254PairingPair {
    pub g1: Bytes64,
    pub g2: Bytes128,
}

#[repr(C)]
pub struct Bls12G1MsmPair {
    pub point: Bytes96,
    pub scalar: Bytes32,
}

#[repr(C)]
pub struct Bls12G2MsmPair {
    pub point: Bytes192,
    pub scalar: Bytes32,
}

#[repr(C)]
pub struct Bls12PairingPair {
    pub g1: Bytes96,
    pub g2: Bytes192,
}

// -------------------------------------------------------------------------
// Hashes
// -------------------------------------------------------------------------

/// Keccak-256 via the OpenVM keccak extension (v2: permutation-level AIRs
/// behind the same one-shot guest API).
#[no_mangle]
pub unsafe extern "C" fn zkvm_keccak256(
    data: *const u8,
    len: usize,
    output: *mut Bytes32,
) -> i32 {
    let input = core::slice::from_raw_parts(data, len);
    (*output).data = openvm_keccak256::keccak256(input);
    ZKVM_EOK
}

/// SHA-256 via the OpenVM sha2 extension. Unlike openvm-keccak256, the sha2
/// guest lib exposes no free function — the one-shot form is an associated
/// function on the digest type, available because this crate disables the
/// `import_sha2` feature (see Cargo.toml).
#[no_mangle]
pub unsafe extern "C" fn zkvm_sha256(
    data: *const u8,
    len: usize,
    output: *mut Bytes32,
) -> i32 {
    let input = core::slice::from_raw_parts(data, len);
    (*output).data = openvm_sha2::Sha256::digest(input);
    ZKVM_EOK
}

/// RIPEMD-160, pure software — OpenVM has no ripemd extension. The
/// precompile is rare enough (and the input small enough) that unaccelerated
/// cycles are acceptable; revisit with a custom extension if profiling
/// disagrees. Digest at bytes [12,32), zero prefix, per the header.
#[no_mangle]
pub unsafe extern "C" fn zkvm_ripemd160(
    data: *const u8,
    len: usize,
    output: *mut Bytes32,
) -> i32 {
    let input = core::slice::from_raw_parts(data, len);
    let digest = ripemd::Ripemd160::digest(input);
    let out = &mut (*output).data;
    out[..12].fill(0);
    out[12..].copy_from_slice(&digest);
    ZKVM_EOK
}

// -------------------------------------------------------------------------
// secp256k1 / secp256r1 (OpenVM-patched k256 / p256)
// -------------------------------------------------------------------------

/// ECRECOVER via openvm-k256. Returns the uncompressed public key without
/// the 0x04 prefix (x || y); the caller keccaks it into an address
/// (zkvm/category/execution/ethereum/core/ecrecover.cpp).
#[no_mangle]
pub unsafe extern "C" fn zkvm_secp256k1_ecrecover(
    msg: *const Bytes32,
    sig: *const Bytes64,
    recid: u8,
    output: *mut Bytes64,
) -> i32 {
    use openvm_k256::ecdsa::{RecoveryId, Signature, VerifyingKey};

    let Ok(mut signature) = Signature::from_slice(&(*sig).data) else {
        return ZKVM_EFAIL;
    };
    // The precompile accepts any s < n; k256 recovery wants low-s. Normalize
    // and flip the recovery id parity to compensate (the revm/k256 pattern).
    let mut recid = recid;
    if let Some(normalized) = signature.normalize_s() {
        signature = normalized;
        recid ^= 1;
    }
    let Some(recovery_id) = RecoveryId::from_byte(recid) else {
        return ZKVM_EFAIL;
    };
    let Ok(key) = VerifyingKey::recover_from_prehash(
        &(*msg).data,
        &signature,
        recovery_id,
    ) else {
        return ZKVM_EFAIL;
    };
    let point = key.to_encoded_point(false);
    (*output).data.copy_from_slice(&point.as_bytes()[1..65]);
    ZKVM_EOK
}

/// secp256k1 ECDSA verification via openvm-k256.
#[no_mangle]
pub unsafe extern "C" fn zkvm_secp256k1_verify(
    msg: *const Bytes32,
    sig: *const Bytes64,
    pubkey: *const Bytes64,
    verified: *mut bool,
) -> i32 {
    use openvm_k256::ecdsa::signature::hazmat::PrehashVerifier as _;
    use openvm_k256::ecdsa::{Signature, VerifyingKey};

    let mut encoded = [0u8; 65];
    encoded[0] = 0x04;
    encoded[1..].copy_from_slice(&(*pubkey).data);
    let Ok(key) = VerifyingKey::from_sec1_bytes(&encoded) else {
        return ZKVM_EFAIL;
    };
    let Ok(signature) = Signature::from_slice(&(*sig).data) else {
        return ZKVM_EFAIL;
    };
    *verified = key.verify_prehash(&(*msg).data, &signature).is_ok();
    ZKVM_EOK
}

/// secp256r1 (P-256, EIP-7212) ECDSA verification via openvm-p256.
#[no_mangle]
pub unsafe extern "C" fn zkvm_secp256r1_verify(
    msg: *const Bytes32,
    sig: *const Bytes64,
    pubkey: *const Bytes64,
    verified: *mut bool,
) -> i32 {
    use openvm_p256::ecdsa::signature::hazmat::PrehashVerifier as _;
    use openvm_p256::ecdsa::{Signature, VerifyingKey};

    let mut encoded = [0u8; 65];
    encoded[0] = 0x04;
    encoded[1..].copy_from_slice(&(*pubkey).data);
    let Ok(key) = VerifyingKey::from_sec1_bytes(&encoded) else {
        return ZKVM_EFAIL;
    };
    let Ok(signature) = Signature::from_slice(&(*sig).data) else {
        return ZKVM_EFAIL;
    };
    *verified = key.verify_prehash(&(*msg).data, &signature).is_ok();
    ZKVM_EOK
}

// -------------------------------------------------------------------------
// MODEXP (0x05)
// -------------------------------------------------------------------------

/// Arbitrary-precision modexp, pure software (aurora-engine-modexp, the
/// same crate revm uses). OpenVM's modular-arithmetic extension only serves
/// moduli fixed at init! time, so it cannot back this precompile; a
/// hint-verify scheme or custom extension is the acceleration path if
/// profiling demands one.
#[no_mangle]
pub unsafe extern "C" fn zkvm_modexp(
    base: *const u8,
    base_len: usize,
    exp: *const u8,
    exp_len: usize,
    modulus: *const u8,
    mod_len: usize,
    output: *mut u8,
) -> i32 {
    let base = core::slice::from_raw_parts(base, base_len);
    let exp = core::slice::from_raw_parts(exp, exp_len);
    let modulus = core::slice::from_raw_parts(modulus, mod_len);
    let result: Vec<u8> = aurora_engine_modexp::modexp(base, exp, modulus);
    if result.len() > mod_len {
        return ZKVM_EFAIL;
    }
    // Big-endian result, left-padded to exactly mod_len bytes.
    let out = core::slice::from_raw_parts_mut(output, mod_len);
    let pad = mod_len - result.len();
    out[..pad].fill(0);
    out[pad..].copy_from_slice(&result);
    ZKVM_EOK
}

// -------------------------------------------------------------------------
// BLAKE2f (0x09)
// -------------------------------------------------------------------------

const BLAKE2B_IV: [u64; 8] = [
    0x6a09e667f3bcc908,
    0xbb67ae8584caa73b,
    0x3c6ef372fe94f82b,
    0xa54ff53a5f1d36f1,
    0x510e527fade682d1,
    0x9b05688c2b3e6c1f,
    0x1f83d9abfb41bd6b,
    0x5be0cd19137e2179,
];

const BLAKE2B_SIGMA: [[usize; 16]; 10] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
];

#[inline(always)]
fn blake2b_g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

/// BLAKE2b compression function F (RFC 7693 / EIP-152), pure software —
/// OpenVM has no blake2 extension. `rounds` is the plain integer value; the
/// EVM-layer big-endian decode already happened in precompiles_impl.hpp.
#[no_mangle]
pub unsafe extern "C" fn zkvm_blake2f(
    rounds: u32,
    h: *mut Bytes64,
    m: *const Bytes128,
    t: *const Bytes16,
    f: u8,
) -> i32 {
    // Bind each buffer once: indexing through the raw pointer directly would
    // autoref per use, which `dangerous_implicit_autorefs` rejects.
    let h = &mut (*h).data;
    let m = &(*m).data;
    let t = &(*t).data;

    let mut state = [0u64; 8];
    for (i, word) in state.iter_mut().enumerate() {
        *word = u64::from_le_bytes(h[i * 8..(i + 1) * 8].try_into().unwrap());
    }
    let mut message = [0u64; 16];
    for (i, word) in message.iter_mut().enumerate() {
        *word = u64::from_le_bytes(m[i * 8..(i + 1) * 8].try_into().unwrap());
    }
    let t0 = u64::from_le_bytes(t[0..8].try_into().unwrap());
    let t1 = u64::from_le_bytes(t[8..16].try_into().unwrap());

    let mut v = [0u64; 16];
    v[..8].copy_from_slice(&state);
    v[8..].copy_from_slice(&BLAKE2B_IV);
    v[12] ^= t0;
    v[13] ^= t1;
    if f != 0 {
        v[14] = !v[14];
    }

    for round in 0..rounds as usize {
        let s = &BLAKE2B_SIGMA[round % 10];
        blake2b_g(&mut v, 0, 4, 8, 12, message[s[0]], message[s[1]]);
        blake2b_g(&mut v, 1, 5, 9, 13, message[s[2]], message[s[3]]);
        blake2b_g(&mut v, 2, 6, 10, 14, message[s[4]], message[s[5]]);
        blake2b_g(&mut v, 3, 7, 11, 15, message[s[6]], message[s[7]]);
        blake2b_g(&mut v, 0, 5, 10, 15, message[s[8]], message[s[9]]);
        blake2b_g(&mut v, 1, 6, 11, 12, message[s[10]], message[s[11]]);
        blake2b_g(&mut v, 2, 7, 8, 13, message[s[12]], message[s[13]]);
        blake2b_g(&mut v, 3, 4, 9, 14, message[s[14]], message[s[15]]);
    }

    for i in 0..8 {
        state[i] ^= v[i] ^ v[i + 8];
        h[i * 8..(i + 1) * 8].copy_from_slice(&state[i].to_le_bytes());
    }
    ZKVM_EOK
}

// -------------------------------------------------------------------------
// Elliptic-curve helpers shared by BN254 and BLS12-381
// -------------------------------------------------------------------------

/// A big-endian hex string as bytes. The curve constants in this module and in
/// `bls12_map` are written as hex so they can be diffed against the specs they
/// come from, rather than as byte arrays.
const fn hex_be<const N: usize>(s: &str) -> [u8; N] {
    let b = s.as_bytes();
    assert!(b.len() == 2 * N);
    let mut out = [0u8; N];
    let mut i = 0;
    while i < N {
        out[i] = hex_nibble(b[2 * i]) * 16 + hex_nibble(b[2 * i + 1]);
        i += 1;
    }
    out
}

/// One hex digit's value. Public so `bls12_map` can share it: its own
/// constants need the bytes reversed, so it cannot reuse `hex_be` itself.
pub const fn hex_nibble(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        _ => panic!("constant contains a non-hex digit"),
    }
}

/// `scalar * point`, MSB-first double-and-add over the big-endian `scalar`.
///
/// Used in place of `IntrinsicCurve::msm` / `CachedMulTable` because every
/// scalar reaching these shims is an arbitrary 256-bit integer: EIP-196 and
/// EIP-2537 both take the scalar as raw bytes with no requirement that it be
/// less than the group order, so it does not fit the curve's `Scalar` type
/// (whose constructors reject anything >= the order). The same routine serves
/// the subgroup checks, where the multiplier *is* the order. The point
/// operations are the accelerated ones, but the ladder is unwindowed — worth
/// revisiting if MSM-heavy contracts turn up in profiling.
pub fn mul_be_bytes<P: Group>(point: &P, scalar: &[u8]) -> P {
    let mut acc = P::IDENTITY;
    for byte in scalar {
        for bit in (0..8).rev() {
            acc.double_assign();
            if (byte >> bit) & 1 == 1 {
                acc += point;
            }
        }
    }
    acc
}

/// Is `point` in the prime-order subgroup? The order is read from the curve's
/// scalar-field modulus rather than restated here, so it cannot drift from
/// `openvm.toml`.
fn in_subgroup<P: Group, S: IntMod>(point: &P) -> bool {
    let mut order: Vec<u8> = S::MODULUS.as_ref().to_vec();
    order.reverse();
    mul_be_bytes(point, &order).is_identity()
}

// -------------------------------------------------------------------------
// BN254 / alt_bn128 (0x06-0x08)
// -------------------------------------------------------------------------

/// Decode an EIP-196 G1 point: `x || y`, 32-byte big-endian each, with
/// `(0, 0)` meaning the point at infinity.
///
/// `ecadd_impl` / `ecmul_impl` / `snarkv_impl` hand the raw calldata straight
/// through (zero-padded, never validated), so every check the EIP demands
/// happens here and a rejection becomes `ZKVM_EFAIL` — which those shims turn
/// into a precompile failure. BN254's G1 has cofactor 1, so being on the curve
/// already implies prime order; no subgroup check is needed.
fn bn254_g1_decode(raw: &[u8; 64]) -> Option<Bn254G1> {
    let x = Bn254Fp::from_be_bytes(&raw[..32])?;
    let y = Bn254Fp::from_be_bytes(&raw[32..])?;
    // `from_xy` checks the curve equation and maps (0, 0) to the identity.
    // The subgroup membership it does not check is vacuous for this curve.
    Bn254G1::from_xy(x, y)
}

fn bn254_g1_encode(point: &Bn254G1, out: &mut [u8; 64]) {
    // OpenVM's modular-arithmetic chips range-check their output limb-wise
    // only, so an intrinsic result is congruent mod p but not necessarily the
    // canonical representative below p. `assert_reduced` constrains that it is
    // before the bytes become a precompile return value.
    point.x().assert_reduced();
    point.y().assert_reduced();
    out[..32].copy_from_slice(point.x().to_be_bytes().as_ref());
    out[32..].copy_from_slice(point.y().to_be_bytes().as_ref());
}

/// Decode an EIP-197 G2 point. Each Fp2 coordinate is encoded imaginary part
/// first (`c1 || c0`) — the opposite of EIP-2537's BLS12-381 layout, which is
/// why the two curves need separate decoders rather than one parameterised
/// helper. G2 has a large cofactor, so the curve equation does not imply prime
/// order and `PairingCheck` makes the subgroup check the caller's job.
fn bn254_g2_decode(raw: &[u8; 128]) -> Option<Bn254G2> {
    let x = Bn254Fp2::new(
        Bn254Fp::from_be_bytes(&raw[32..64])?,
        Bn254Fp::from_be_bytes(&raw[..32])?,
    );
    let y = Bn254Fp2::new(
        Bn254Fp::from_be_bytes(&raw[96..128])?,
        Bn254Fp::from_be_bytes(&raw[64..96])?,
    );
    // As bn254_g1_decode, plus the subgroup check that follows.
    let point = Bn254G2::from_xy(x, y)?;
    in_subgroup::<_, Bn254Scalar>(&point).then_some(point)
}

/// BN254 G1 addition (EIP-196) over the OpenVM ECC intrinsics.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bn254_g1_add(
    p1: *const Bytes64,
    p2: *const Bytes64,
    result: *mut Bytes64,
) -> i32 {
    let (Some(p1), Some(p2)) =
        (bn254_g1_decode(&(*p1).data), bn254_g1_decode(&(*p2).data))
    else {
        return ZKVM_EFAIL;
    };
    bn254_g1_encode(&(p1 + &p2), &mut (*result).data);
    ZKVM_EOK
}

/// BN254 G1 scalar multiplication (EIP-196). The scalar is an arbitrary
/// 256-bit integer, not a reduced group element.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bn254_g1_mul(
    point: *const Bytes64,
    scalar: *const Bytes32,
    result: *mut Bytes64,
) -> i32 {
    let Some(point) = bn254_g1_decode(&(*point).data) else {
        return ZKVM_EFAIL;
    };
    bn254_g1_encode(
        &mul_be_bytes(&point, &(*scalar).data),
        &mut (*result).data,
    );
    ZKVM_EOK
}

/// BN254 pairing check (EIP-197): does `prod_i e(P_i, Q_i) == 1`?
#[no_mangle]
pub unsafe extern "C" fn zkvm_bn254_pairing(
    pairs: *const Bn254PairingPair,
    num_pairs: usize,
    verified: *mut bool,
) -> i32 {
    let mut ps = Vec::with_capacity(num_pairs);
    let mut qs = Vec::with_capacity(num_pairs);
    for pair in core::slice::from_raw_parts(pairs, num_pairs) {
        let (Some(g1), Some(g2)) =
            (bn254_g1_decode(&pair.g1.data), bn254_g2_decode(&pair.g2.data))
        else {
            return ZKVM_EFAIL;
        };
        // e(O, Q) = e(P, O) = 1, so a pair with an infinity point contributes
        // nothing to the product. Dropping it is not just an optimisation:
        // the Miller loop has no affine representation of infinity, and
        // EIP-197 explicitly permits infinity as input.
        if g1.is_identity() || g2.is_identity() {
            continue;
        }
        let (x, y) = g1.into_coords();
        ps.push(AffinePoint::new(x, y));
        let (x, y) = g2.into_coords();
        qs.push(AffinePoint::new(x, y));
    }
    // An empty product is 1. This covers both a zero-length input and one
    // where every pair had an infinity point.
    *verified = ps.is_empty() || Bn254::pairing_check(&ps, &qs).is_ok();
    ZKVM_EOK
}

// -------------------------------------------------------------------------
// BLS12-381 (0x0b-0x0f)
// -------------------------------------------------------------------------
//
// The encodings here are the *raw* ones from precompiles_impl.hpp, not
// EIP-2537's: `evm_g1_to_zkvm` / `evm_g2_to_zkvm` have already stripped the
// 16-byte zero pad from each 64-byte EVM field element and rejected any
// coordinate >= p. What reaches these shims is 48-byte big-endian limbs, Fp2
// as `c0 || c1` (unlike BN254 above), and an all-zero point meaning infinity.
// The `from_be_bytes` range check is therefore redundant with the C++ one —
// kept because it is how the field element is built either way, and because
// this ABI is also reachable from a caller that does not pre-validate.
//
// Which checks each precompile needs is not uniform, and EIP-2537 says so
// explicitly: G1ADD and G2ADD require only that the inputs be on the curve,
// while the MSMs and the pairing also require prime-order subgroup membership.
// BLS12-381 has a non-trivial cofactor in *both* groups, so unlike BN254 G1
// the curve equation implies nothing about the subgroup on either side.

fn bls_g1_decode(raw: &[u8; 96]) -> Option<BlsG1> {
    let x = BlsFp::from_be_bytes(&raw[..48])?;
    let y = BlsFp::from_be_bytes(&raw[48..])?;
    // `from_xy` checks the curve equation and maps (0, 0) to the identity.
    // Subgroup membership is the caller's to demand.
    BlsG1::from_xy(x, y)
}

fn bls_g1_encode(point: &BlsG1, out: &mut [u8; 96]) {
    // See bn254_g1_encode for why the coordinates are asserted reduced.
    point.x().assert_reduced();
    point.y().assert_reduced();
    out[..48].copy_from_slice(point.x().to_be_bytes().as_ref());
    out[48..].copy_from_slice(point.y().to_be_bytes().as_ref());
}

fn bls_g2_decode(raw: &[u8; 192]) -> Option<BlsG2> {
    let x = BlsFp2::new(
        BlsFp::from_be_bytes(&raw[..48])?,
        BlsFp::from_be_bytes(&raw[48..96])?,
    );
    let y = BlsFp2::new(
        BlsFp::from_be_bytes(&raw[96..144])?,
        BlsFp::from_be_bytes(&raw[144..])?,
    );
    // As bls_g1_decode.
    BlsG2::from_xy(x, y)
}

fn bls_g2_encode(point: &BlsG2, out: &mut [u8; 192]) {
    let (x, y) = (point.x(), point.y());
    for (dst, limb) in out
        .chunks_exact_mut(48)
        .zip([&x.c0, &x.c1, &y.c0, &y.c1])
    {
        limb.assert_reduced();
        dst.copy_from_slice(limb.to_be_bytes().as_ref());
    }
}

/// BLS12-381 G1 addition (EIP-2537 0x0b). On-curve only — no subgroup check.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bls12_g1_add(
    p1: *const Bytes96,
    p2: *const Bytes96,
    result: *mut Bytes96,
) -> i32 {
    let (Some(p1), Some(p2)) =
        (bls_g1_decode(&(*p1).data), bls_g1_decode(&(*p2).data))
    else {
        return ZKVM_EFAIL;
    };
    bls_g1_encode(&(p1 + &p2), &mut (*result).data);
    ZKVM_EOK
}

/// BLS12-381 G1 multi-scalar multiplication (EIP-2537 0x0c). Subgroup check
/// required on every input point.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bls12_g1_msm(
    pairs: *const Bls12G1MsmPair,
    num_pairs: usize,
    result: *mut Bytes96,
) -> i32 {
    let mut acc = <BlsG1 as Group>::IDENTITY;
    for pair in core::slice::from_raw_parts(pairs, num_pairs) {
        let Some(point) = bls_g1_decode(&pair.point.data) else {
            return ZKVM_EFAIL;
        };
        if !in_subgroup::<_, BlsScalar>(&point) {
            return ZKVM_EFAIL;
        }
        acc += &mul_be_bytes(&point, &pair.scalar.data);
    }
    bls_g1_encode(&acc, &mut (*result).data);
    ZKVM_EOK
}

/// BLS12-381 G2 addition (EIP-2537 0x0d). On-curve only — no subgroup check.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bls12_g2_add(
    p1: *const Bytes192,
    p2: *const Bytes192,
    result: *mut Bytes192,
) -> i32 {
    let (Some(p1), Some(p2)) =
        (bls_g2_decode(&(*p1).data), bls_g2_decode(&(*p2).data))
    else {
        return ZKVM_EFAIL;
    };
    bls_g2_encode(&(p1 + &p2), &mut (*result).data);
    ZKVM_EOK
}

/// BLS12-381 G2 multi-scalar multiplication (EIP-2537 0x0e). Subgroup check
/// required on every input point.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bls12_g2_msm(
    pairs: *const Bls12G2MsmPair,
    num_pairs: usize,
    result: *mut Bytes192,
) -> i32 {
    let mut acc = <BlsG2 as Group>::IDENTITY;
    for pair in core::slice::from_raw_parts(pairs, num_pairs) {
        let Some(point) = bls_g2_decode(&pair.point.data) else {
            return ZKVM_EFAIL;
        };
        if !in_subgroup::<_, BlsScalar>(&point) {
            return ZKVM_EFAIL;
        }
        acc += &mul_be_bytes(&point, &pair.scalar.data);
    }
    bls_g2_encode(&acc, &mut (*result).data);
    ZKVM_EOK
}

/// BLS12-381 pairing check (EIP-2537 0x0f). Both groups need the subgroup
/// check; infinity pairs drop out as in `zkvm_bn254_pairing`.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bls12_pairing(
    pairs: *const Bls12PairingPair,
    num_pairs: usize,
    verified: *mut bool,
) -> i32 {
    let mut ps = Vec::with_capacity(num_pairs);
    let mut qs = Vec::with_capacity(num_pairs);
    for pair in core::slice::from_raw_parts(pairs, num_pairs) {
        let (Some(g1), Some(g2)) =
            (bls_g1_decode(&pair.g1.data), bls_g2_decode(&pair.g2.data))
        else {
            return ZKVM_EFAIL;
        };
        if !in_subgroup::<_, BlsScalar>(&g1) || !in_subgroup::<_, BlsScalar>(&g2)
        {
            return ZKVM_EFAIL;
        }
        if g1.is_identity() || g2.is_identity() {
            continue;
        }
        let (x, y) = g1.into_coords();
        ps.push(AffinePoint::new(x, y));
        let (x, y) = g2.into_coords();
        qs.push(AffinePoint::new(x, y));
    }
    *verified = ps.is_empty() || Bls12_381::pairing_check(&ps, &qs).is_ok();
    ZKVM_EOK
}

/// BLS12-381 map field element to G1 (EIP-2537 0x10). See `bls12_map`.
#[no_mangle]
pub unsafe extern "C" fn zkvm_bls12_map_fp_to_g1(
    field_element: *const Bytes48,
    result: *mut Bytes96,
) -> i32 {
    let Some(point) = crate::bls12_map::map_fp_to_g1(&(*field_element).data) else {
        return ZKVM_EFAIL;
    };
    bls_g1_encode(&point, &mut (*result).data);
    ZKVM_EOK
}

/// BLS12-381 map Fp2 element to G2 (EIP-2537 0x11).
#[no_mangle]
pub unsafe extern "C" fn zkvm_bls12_map_fp2_to_g2(
    field_element: *const Bytes96,
    result: *mut Bytes192,
) -> i32 {
    let Some(point) = crate::bls12_map::map_fp2_to_g2(&(*field_element).data) else {
        return ZKVM_EFAIL;
    };
    bls_g2_encode(&point, &mut (*result).data);
    ZKVM_EOK
}

// -------------------------------------------------------------------------
// KZG point evaluation (0x0a)
// -------------------------------------------------------------------------
//
// openvm v2.0.1 ships no KZG support of any kind (the only candidate is the
// separate axiom-crypto/openvm-kzg repo, whose v2 compatibility is
// unverified), so this is `verify_kzg_proof` written out over the accelerated
// BLS12-381 pairing above. Only one trusted-setup element is needed: the
// polynomial commitment scheme's G2 side is `[tau]_2` alone, and the G1 side
// of the check is supplied by the caller.

/// The BLS12-381 G2 generator, in the raw `x.c0 || x.c1 || y.c0 || y.c1`
/// layout `bls_g2_decode` expects. Not available from openvm: `CyclicGroup` is
/// implemented for `Bls12_381G1Affine` but not for the software G2 type.
const KZG_G2_GENERATOR: [u8; 192] = hex_be(concat!(
    "024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8",
    "13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e",
    "0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801",
    "0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
));

/// `[tau]_2` from the Ethereum KZG ceremony — element 1 of the monomial-form
/// G2 trusted setup, decompressed from `third_party/c-kzg-4844`'s
/// `src/trusted_setup.txt` (element 0 of which is the generator above, which
/// is how the extraction was checked).
const KZG_TAU_G2: [u8; 192] = hex_be(concat!(
    "185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2",
    "15bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72",
    "014353bdb96b626dd7d5ee8599d1fca2131569490e28de18e82451a496a9c9794ce26d105941f383ee689bfbbb832a99",
    "1666c54b0a32529503432fcae0181b4bef79de09fc63671fda5ed1ba9bfa07899495346f3d7ac9cd23048ef30d0a154f",
));

/// Decompress a 48-byte G1 point in the zcash encoding EIP-4844 uses for KZG
/// commitments and proofs: the top three bits of byte 0 are the compression,
/// infinity and sign flags, and the remaining 381 bits are `x` big-endian.
///
/// openvm's `FromCompressed::decompress` does not fit — it picks `y` by
/// *parity*, whereas this encoding picks the lexicographically larger of `y`
/// and `p - y`. Subgroup membership is checked here because `validate_kzg_g1`
/// in the EIP-4844 spec requires it of both inputs.
fn kzg_g1_decompress(raw: &[u8; 48]) -> Option<BlsG1> {
    let flags = raw[0] >> 5;
    if flags & 0b100 == 0 {
        // The uncompressed form is 96 bytes and cannot appear in a 48-byte
        // field, so a clear compression bit is simply malformed.
        return None;
    }
    let mut xb = *raw;
    xb[0] &= 0x1f;
    if flags & 0b010 != 0 {
        // Point at infinity: the sign bit must be clear and x must be zero.
        return (flags & 0b001 == 0 && xb.iter().all(|b| *b == 0))
            .then(|| <BlsG1 as Group>::IDENTITY);
    }
    let x = BlsFp::from_be_bytes(&xb)?;
    let y = (&x * &x * &x + BlsFp::from_u8(4)).sqrt()?;
    let neg = -y.clone();
    // Both branches feed a byte comparison, which is only meaningful on the
    // canonical representative; see bn254_g1_encode.
    y.assert_reduced();
    neg.assert_reduced();
    let larger = y.to_be_bytes() > neg.to_be_bytes();
    let y = if larger == (flags & 0b001 != 0) { y } else { neg };
    // `from_xy_unchecked` skips the curve-equation check, which is sound here
    // because y was computed as a square root of that equation at x. It is not
    // the identity either — that case returned above. The subgroup check
    // follows.
    let point = BlsG1::from_xy_unchecked(x, y);
    in_subgroup::<_, BlsScalar>(&point).then_some(point)
}

/// EIP-4844 point evaluation: does `p(z) = y` for the polynomial `commitment`
/// commits to, as attested by `proof`?
///
/// The KZG check `e(proof, [tau]_2 - [z]_2) == e(commitment - [y]_1, [1]_2)`
/// is rearranged into a single product so it can go through `pairing_check`:
///
/// ```text
/// e(proof, [tau]_2 - [z]_2) * e(commitment - [y]_1, -[1]_2) == 1
/// ```
///
/// The versioned-hash check that EIP-4844 also requires happens on the C++
/// side, in `point_evaluation_impl`.
#[no_mangle]
pub unsafe extern "C" fn zkvm_kzg_point_eval(
    commitment: *const Bytes48,
    z: *const Bytes32,
    y: *const Bytes32,
    proof: *const Bytes48,
    verified: *mut bool,
) -> i32 {
    // EIP-4844 requires both field elements to be canonical elements of the
    // scalar field; `from_be_bytes` rejects anything >= the modulus.
    let (Some(z), Some(y)) = (
        BlsScalar::from_be_bytes(&(*z).data),
        BlsScalar::from_be_bytes(&(*y).data),
    ) else {
        return ZKVM_EFAIL;
    };
    let (Some(commitment), Some(proof)) = (
        kzg_g1_decompress(&(*commitment).data),
        kzg_g1_decompress(&(*proof).data),
    ) else {
        return ZKVM_EFAIL;
    };
    let (Some(g2), Some(tau)) = (
        bls_g2_decode(&KZG_G2_GENERATOR),
        bls_g2_decode(&KZG_TAU_G2),
    ) else {
        return ZKVM_EFAIL;
    };

    let g1 = <BlsG1 as openvm_ecc_guest::CyclicGroup>::GENERATOR;
    let pairs = [
        (proof, tau - mul_be_bytes(&g2, z.to_be_bytes().as_ref())),
        (
            commitment - mul_be_bytes(&g1, y.to_be_bytes().as_ref()),
            -g2,
        ),
    ];

    let mut ps = Vec::with_capacity(2);
    let mut qs = Vec::with_capacity(2);
    for (p, q) in pairs {
        // As in the pairing shims: a term with an infinity point evaluates to
        // 1 and has no affine representation in the Miller loop. Both terms
        // dropping is a legitimate outcome — an infinity commitment with a
        // matching infinity proof satisfies the check.
        if p.is_identity() || q.is_identity() {
            continue;
        }
        let (x, y) = p.into_coords();
        ps.push(AffinePoint::new(x, y));
        let (x, y) = q.into_coords();
        qs.push(AffinePoint::new(x, y));
    }
    *verified = ps.is_empty() || Bls12_381::pairing_check(&ps, &qs).is_ok();
    ZKVM_EOK
}
