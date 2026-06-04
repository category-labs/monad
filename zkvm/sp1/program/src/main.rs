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

#![no_main]
sp1_zkvm::entrypoint!(main);

use std::sync::OnceLock;

// The C++ guest (zkvm/guest/ffi.cpp) calls read_input / write_output from
// the eth-act standard interface (zkvm/core/zkvm_io.h). ZisK supplies those
// symbols natively via ziskos; SP1 has no equivalent, so this program
// provides a thin shim that maps the same ABI onto sp1_zkvm::io.
//
// `read_input` is required to be idempotent (Decision: matches the eth-act
// contract), so we cache the witness on first call.
//
// zkvm_halt (declared in zkvm/core/zkvm_halt.h) is similarly shimmed onto
// sp1_zkvm::syscalls::syscall_halt.
//
// sys_alloc_aligned (used by the C++ libc/libstdc++ stubs in zkvm/core/) is
// supplied by sp1-zkvm itself — no Rust-side allocator shim needed here.

static INPUT: OnceLock<Vec<u8>> = OnceLock::new();

#[no_mangle]
pub unsafe extern "C" fn read_input(buf_ptr: *mut *const u8, buf_size: *mut usize) {
    let input = INPUT.get_or_init(sp1_zkvm::io::read_vec);
    *buf_ptr = input.as_ptr();
    *buf_size = input.len();
}

#[no_mangle]
pub unsafe extern "C" fn write_output(output: *const u8, size: usize) {
    let slice = core::slice::from_raw_parts(output, size);
    sp1_zkvm::io::commit_slice(slice);
}

#[no_mangle]
pub unsafe extern "C" fn zkvm_halt(status: i32) -> ! {
    sp1_zkvm::syscalls::syscall_halt(status as u8)
}

// zkvm_keccak256: standardized zkVM accelerator API for keccak-256 (see
// zkvm/core/zkvm_accelerators.h). ZisK provides this natively; for SP1 we
// shim it with tiny-keccak. Performance can be improved later by patching
// tiny-keccak to lower its keccakf to sp1's syscall_keccak_permute.
#[no_mangle]
pub unsafe extern "C" fn zkvm_keccak256(
    data: *const u8,
    len: usize,
    output: *mut u8,
) -> i32 {
    use tiny_keccak::{Hasher, Keccak};
    let input = core::slice::from_raw_parts(data, len);
    let out = core::slice::from_raw_parts_mut(output, 32);
    let mut hasher = Keccak::v256();
    hasher.update(input);
    hasher.finalize(out);
    0 // ZKVM_EOK
}

extern "C" {
    fn monad_zkvm_execute_witness();
}

fn main() {
    unsafe { monad_zkvm_execute_witness() };
}
