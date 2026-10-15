// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

//! The zkvm_* accelerators of zkvm_accelerators.h on Airbender, over
//! airbender-crypto with its "proving" features (bigint and keccak
//! delegations), the same code ZKsync OS proves blocks with.

#![no_std]

use airbender_crypto::ripemd160::{Digest as _, Ripemd160};
use airbender_crypto::secp256k1::{hooks::DefaultSecp256k1Hooks, recover_from_bytes_with_hooks};
use airbender_crypto::sha256::Sha256;
use core::alloc::{GlobalAlloc, Layout};

extern "C" {
    fn sys_alloc_aligned(size: usize, align: usize) -> *mut u8;
    fn abort() -> !;
    fn monad_zkvm_airbender_print(s: *const u8, len: usize);
}

const ZKVM_EOK: i32 = 0;
const ZKVM_EFAIL: i32 = -1;

/// The guest's bump arena (runtime.c); frees are dropped, as the C++ side's are.
struct Arena;

unsafe impl GlobalAlloc for Arena {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        sys_alloc_aligned(layout.size(), layout.align())
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static ARENA: Arena = Arena;

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    const MSG: &[u8] = b"panic in the Airbender accelerators";
    unsafe {
        monad_zkvm_airbender_print(MSG.as_ptr(), MSG.len());
        abort()
    }
}

/// ecrecover's public key, x || y big-endian. `recid` is the parity of y;
/// Ethereum never recovers from an `r` reduced past the group order.
#[no_mangle]
pub unsafe extern "C" fn zkvm_secp256k1_ecrecover(
    msg: *const [u8; 32],
    sig: *const [u8; 64],
    recid: u8,
    output: *mut [u8; 64],
) -> i32 {
    if recid > 1 {
        return ZKVM_EFAIL;
    }
    let sig = &*sig;
    let (r, s) = sig.split_at(32);
    let (r, s): (&[u8; 32], &[u8; 32]) = (r.try_into().unwrap(), s.try_into().unwrap());
    match recover_from_bytes_with_hooks(&*msg, r, s, recid == 1, &mut DefaultSecp256k1Hooks) {
        Ok(point) => {
            let (x, y) = (*output).split_at_mut(32);
            point.write_coordinates(x.try_into().unwrap(), y.try_into().unwrap());
            ZKVM_EOK
        }
        Err(_) => ZKVM_EFAIL,
    }
}

#[no_mangle]
pub unsafe extern "C" fn zkvm_sha256(data: *const u8, len: usize, output: *mut [u8; 32]) -> i32 {
    use airbender_crypto::sha256::Digest as _;
    let input = core::slice::from_raw_parts(data, len);
    (*output).copy_from_slice(&Sha256::digest(input));
    ZKVM_EOK
}

/// The 20-byte digest right-aligned, after 12 zero bytes, as the precompile
/// returns it (and as ZisK's accelerator writes it).
#[no_mangle]
pub unsafe extern "C" fn zkvm_ripemd160(data: *const u8, len: usize, output: *mut [u8; 32]) -> i32 {
    let input = core::slice::from_raw_parts(data, len);
    let out = &mut *output;
    out[..12].fill(0);
    out[12..].copy_from_slice(&Ripemd160::digest(input));
    ZKVM_EOK
}
