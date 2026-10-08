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

//! ecAdd and ecMul on little-endian limbs: zkvm_bn254_g1_add and
//! zkvm_bn254_g1_mul without their byte conversions. zisklib reads a point's
//! 64 big-endian bytes one at a time, a load, a shift and an or each, and
//! writes the result back the same way; the guest converts a word with one
//! load and one byte swap. The arithmetic and its checks -- coordinates in
//! the field, points on the curve, the identity -- are zisklib's, unchanged.

use ziskos::zisklib::{add_complete_safe_bn254, scalar_mul_complete_safe_bn254};

/// `p1 + p2`, as zkvm_bn254_g1_add computes it; false where it fails, and
/// `out` then untouched.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_bn254_g1_add(
    p1: *const [u64; 8],
    p2: *const [u64; 8],
    out: *mut [u64; 8],
) -> bool {
    match add_complete_safe_bn254(&*p1, &*p2) {
        Ok(r) => {
            *out = r;
            true
        }
        Err(_) => false,
    }
}

/// `k * p`, as zkvm_bn254_g1_mul computes it; false where it fails, and
/// `out` then untouched.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_bn254_g1_mul(
    p: *const [u64; 8],
    k: *const [u64; 4],
    out: *mut [u64; 8],
) -> bool {
    match scalar_mul_complete_safe_bn254(&*p, &*k) {
        Ok(r) => {
            *out = r;
            true
        }
        Err(_) => false,
    }
}
