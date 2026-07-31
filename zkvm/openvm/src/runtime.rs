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

//! The eth-act runtime ABI (zkvm/core/zkvm_io.h, zkvm_halt.h, libc.hpp) on
//! OpenVM primitives.
//!
//! On ZisK these symbols come from ziskos; on SP1 from libzkevm.a. OpenVM has
//! no eth-act runtime library, so this guest crate provides all of them.
//! Everything here is single-threaded by construction (rv32im, no threads),
//! so plain `static mut` state is sound.

use alloc::vec::Vec;
use core::ptr::addr_of_mut;

// -------------------------------------------------------------------------
// zkvm_io.h
// -------------------------------------------------------------------------

static mut INPUT: Option<(usize, usize)> = None;

/// eth-act `read_input`: expose the first (and only) input record.
///
/// The header requires idempotency — repeated calls return the same pointer
/// and do not advance any cursor — so the `openvm::io::read_vec()` result is
/// fetched once, leaked (the guest never frees), and cached. The host driver
/// must therefore frame the witness as exactly one `StdIn::write_bytes`
/// vector, mirroring SP1's single `write_slice`.
#[no_mangle]
pub unsafe extern "C" fn read_input(
    buf_ptr: *mut *const u8,
    buf_size: *mut usize,
) {
    let slot = addr_of_mut!(INPUT);
    if (*slot).is_none() {
        let payload = openvm::io::read_vec();
        let len = payload.len();
        let ptr = payload.leak().as_ptr();
        *slot = Some((ptr as usize, len));
    }
    let (ptr, len) = (*slot).unwrap();
    *buf_ptr = ptr as *const u8;
    *buf_size = len;
}

static mut OUTPUT: Vec<u8> = Vec::new();

/// eth-act `write_output`: append to the guest's committed output.
///
/// OpenVM's user public values are an array of 4-byte words (address space
/// 3, zero by default), written via `reveal_u32(word, word_index)`. Appends
/// are byte-granular, so the full output is accumulated in a shadow buffer
/// and every word covering new bytes is (re-)revealed. The witness guest
/// emits exactly one 32-byte record (the post-state root); the precompile
/// test guest emits a short PR01 summary. The word count must fit the
/// `num_public_values` configured in openvm.toml.
#[no_mangle]
pub unsafe extern "C" fn write_output(output: *const u8, size: usize) {
    let buf = &mut *addr_of_mut!(OUTPUT);
    let first_dirty_word = buf.len() / 4;
    buf.extend_from_slice(core::slice::from_raw_parts(output, size));
    for word_idx in first_dirty_word..buf.len().div_ceil(4) {
        let mut word = [0u8; 4];
        let start = word_idx * 4;
        let end = usize::min(start + 4, buf.len());
        word[..end - start].copy_from_slice(&buf[start..end]);
        openvm::io::reveal_u32(u32::from_le_bytes(word), word_idx);
    }
}

// -------------------------------------------------------------------------
// zkvm_halt.h
// -------------------------------------------------------------------------

/// eth-act `zkvm_halt`: terminate the guest with the given status.
///
/// OpenVM's `terminate` custom instruction takes the exit code as an
/// *immediate*, so `openvm_platform::rust_rt::terminate` is generic over a
/// const exit code and a runtime status cannot be passed through. The status is
/// therefore collapsed to the 0/1 the guest actually uses — ffi.cpp and the
/// core shims only ever halt with 0 or 1.
#[no_mangle]
pub extern "C" fn zkvm_halt(status: i32) -> ! {
    if status == 0 {
        openvm::platform::rust_rt::terminate::<0>();
    } else {
        openvm::platform::rust_rt::terminate::<1>();
    }
    // `terminate` is not marked `!` upstream even though the instruction never
    // returns, so the guest must be told this point is unreachable.
    unreachable!()
}

// -------------------------------------------------------------------------
// libc.hpp
// -------------------------------------------------------------------------
//
// eth-act's `sys_alloc_aligned` — the primitive under the C++ bump allocator in
// zkvm/core/libc.cpp (malloc / operator new; `free` is a no-op) — needs no shim
// here. `openvm-platform` already exports it under its `rust-runtime` feature,
// which the `openvm` crate enables unconditionally, and it is the same bump
// allocator backing Rust's `#[global_allocator]`. Its semantics already match
// what the C++ side expects: allocation-only, word-minimum alignment, and it
// terminates rather than returning null when the 512 MB address space is
// exhausted. Defining one here would be a duplicate symbol.

// -------------------------------------------------------------------------
// Static constructors
// -------------------------------------------------------------------------

/// Run the C++ archive's `.init_array` (RLP encoder tables, commit_builder /
/// partial_trie_db statics, ...). OpenVM's `__start` never runs it, exactly like
/// SP1's — where main.c does this walk (see patch_zkvm_ld in build-support for
/// the SP1 story).
///
/// The boundary symbols come from the final link: rust-lld synthesizes them and
/// treats `.init_array` as a GC root, so the range is populated even under
/// `--gc-sections`. That last part is what makes an empty range safe to read as
/// "nothing to do": a member's constructors are retained whenever the member is
/// pulled into the link at all, so the range is empty only when no ctor-bearing
/// object was needed. The precompile-test guest is exactly that case — none of
/// the ctor-bearing objects are precompile code — while the witness guest gets
/// 12 constructors.
pub fn run_init_array() {
    extern "C" {
        static __init_array_start: [unsafe extern "C" fn(); 0];
        static __init_array_end: [unsafe extern "C" fn(); 0];
    }
    unsafe {
        let mut ctor = __init_array_start.as_ptr();
        let end = __init_array_end.as_ptr();
        while ctor < end {
            (*ctor)();
            ctor = ctor.add(1);
        }
    }
}
