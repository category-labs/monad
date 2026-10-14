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

// C ABI for zisklib GLV secp256k1 multiplication using add/dbl precompiles.
// Points use eight u64 limbs: little-endian x, then y. C++ converts SEC1 wire
// bytes in l2_ecdh.hpp. The generator is on the C++ side because zisklib's
// constants module is private.

use ziskos::zisklib::{
    glv_scalar_mul_secp256k1, is_on_curve_secp256k1, lift_x_secp256k1,
};

const OK: i32 = 0;
const FAIL: i32 = -1;

/// out = k*q; FAIL for an invalid/identity q or an identity product. The
/// caller treats failure as a rejected transaction.
///
/// # Safety
/// k points to 4 readable u64s, q to 8, and out to 8 writable u64s.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_secp256k1_mul(
    k: *const u64,
    q: *const u64,
    out: *mut u64,
) -> i32 {
    let k: &[u64; 4] = &*(k as *const [u64; 4]);
    let q: &[u64; 8] = &*(q as *const [u64; 8]);

    // Enforce zisklib's on-curve and non-identity preconditions. The C++
    // caller checks canonical coordinates first: is_on_curve_secp256k1
    // reduces inputs and cannot reject non-canonical encodings.
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

/// Return OK for a non-identity curve point, FAIL otherwise. The caller must
/// check canonical coordinates.
///
/// # Safety
/// q points to 8 readable u64s.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_secp256k1_is_valid(q: *const u64) -> i32 {
    let q: &[u64; 8] = &*(q as *const [u64; 8]);
    if q == &[0u64; 8] || !is_on_curve_secp256k1(q) {
        return FAIL;
    }
    OK
}

/// Lift x to the point with the requested y parity; FAIL for a non-residue.
///
/// # Safety
/// x points to 4 readable u64s; out to 8 writable u64s.
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
