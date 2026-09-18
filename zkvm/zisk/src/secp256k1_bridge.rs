// Copyright (C) 2026 Category Labs, Inc.
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

// A C entry to ziskos' secp256k1 scalar multiplication, for the L2 guest's
// ECDH. zisklib already rides the `secp256k1_add` and `secp256k1_dbl`
// precompiles and already implements the GLV endomorphism, so there is no curve
// to write here -- only the ABI.
//
// Unlike keccak and Poseidon2, where zkvm/guest emits the precompile marker in
// place because the wrapper is two instructions and the call would cost more
// than the body, a scalar multiplication is a couple of hundred precompile
// operations: the call is free by comparison, so going through Rust is right.
//
// Points are ziskos' own layout -- eight u64 limbs, x then y, each half
// little-endian in its limbs. zkvm/guest/l2_ecdh.hpp converts from the wire's
// big-endian bytes and pins that convention with a test.
//
// The generator is NOT taken from here: zisklib's `constants` module is private
// (`mod constants;`, not `pub use`), so G is unreachable. It lives on the C++
// side instead, and monad_zkvm_secp256k1_mul serves both k*R and k*G.

use ziskos::zisklib::{
    glv_scalar_mul_secp256k1, is_on_curve_secp256k1, lift_x_secp256k1,
};

const OK: i32 = 0;
const FAIL: i32 = -1;

/// `out = k * q`. Returns FAIL when `q` is not a valid non-identity curve point
/// or the product is the identity. Both are deterministic rejections of one
/// transaction rather than faults: the caller consumes the queue entry and
/// moves on, which is what the protocol requires of every rejection.
///
/// # Safety
/// `k` must point to 4 readable u64s, `q` to 8 readable ones, and `out` to 8
/// writable ones.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_secp256k1_mul(
    k: *const u64,
    q: *const u64,
    out: *mut u64,
) -> i32 {
    let k: &[u64; 4] = &*(k as *const [u64; 4]);
    let q: &[u64; 8] = &*(q as *const [u64; 8]);

    // zisklib documents on-curve, non-identity and canonical coordinates as a
    // PRECONDITION of glv_scalar_mul_secp256k1, so it is checked rather than
    // assumed: an unchecked call on a forged point is exactly what a prover
    // would reach for. Two of the three are checked here. CANONICITY IS NOT:
    // is_on_curve_secp256k1 only tests y^2 == x^3 + 7 through field operations
    // that reduce their inputs, so it would accept a coordinate at or above the
    // field size. The C++ caller tests that, on the bytes, before it gets
    // here -- see l2_point_is_valid.
    if q == &[0u64; 8] || !is_on_curve_secp256k1(q) {
        return FAIL;
    }
    match glv_scalar_mul_secp256k1(k, q) {
        Some(p) => {
            core::ptr::copy_nonoverlapping(p.as_ptr(), out, 8);
            OK
        }
        None => FAIL,
    }
}

/// True when `q` is a non-identity point satisfying the curve equation.
/// Canonicity is the caller's, as above. Exposed on its own so the C++ side can
/// check its compiled operator key and its copy of the generator against
/// ziskos' own curve equation rather than against a second implementation of
/// it -- which is what makes a transcription error in either a hard failure at
/// startup instead of a wrong answer.
///
/// # Safety
/// `q` must point to 8 readable u64s.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_secp256k1_is_valid(q: *const u64) -> i32 {
    let q: &[u64; 8] = &*(q as *const [u64; 8]);
    if q == &[0u64; 8] || !is_on_curve_secp256k1(q) {
        return FAIL;
    }
    OK
}

/// `out = lift_x(x, y_is_odd)` -- the point whose x-coordinate is `x` and whose
/// y has the given parity. Returns FAIL when x is not the abscissa of any curve
/// point, which is a deterministic rejection like the others.
///
/// This is how a 33-byte compressed R on the wire becomes a point, and the
/// decompression IS the curve-membership check: there is no separate on-curve
/// test to forget.
///
/// # Safety
/// `x` must point to 4 readable u64s and `out` to 8 writable ones.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_secp256k1_lift_x(
    x: *const u64,
    y_is_odd: i32,
    out: *mut u64,
) -> i32 {
    let x: &[u64; 4] = &*(x as *const [u64; 4]);
    match lift_x_secp256k1(x, y_is_odd != 0) {
        Ok(p) => {
            core::ptr::copy_nonoverlapping(p.as_ptr(), out, 8);
            OK
        }
        Err(_) => FAIL,
    }
}
