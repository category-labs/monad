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
ziskos::entrypoint!(main);

// The C++ guest (zkvm/guest/ffi.cpp) owns input and output via the eth-act
// standard interface (zkvm/core/zkvm_io.h): it calls read_input to fetch the
// RLP-encoded witness and write_output to emit the 32-byte post-state root.
// ziskos supplies both symbols at link time, so Rust just dispatches.
//
// zkvm_halt (declared in zkvm/core/zkvm_halt.h) has no ziskos equivalent;
// we issue the same RISC-V Linux exit syscall (a7 = 93) that ziskos's own
// _start ends on, so the prover terminates with the requested status.

extern "C" {
    fn monad_zkvm_execute_witness();
}

#[no_mangle]
pub unsafe extern "C" fn zkvm_halt(status: i32) -> ! {
    core::arch::asm!(
        "ecall",
        in("a0") status,
        in("a7") 93i32,
        options(noreturn),
    );
}

fn main() {
    unsafe { monad_zkvm_execute_witness() };
}
