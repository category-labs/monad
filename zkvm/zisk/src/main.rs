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

// zkvm/guest/execute_witness.cpp reads the RLP witness and writes the 32-byte
// post-state root through the eth-act I/O functions supplied by ziskos.
extern "C" {
    fn monad_zkvm_execute_witness();
}

// Implement the C++ halt ABI with ZisK's exit syscall (a7 = 93, a0 = status).
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
