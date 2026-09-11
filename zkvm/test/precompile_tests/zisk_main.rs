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

// ZisK entry for the precompile golden-vector test guest. Mirrors the witness
// entry (zkvm/zisk/src/main.rs) but hands control to the precompile-test C++
// entry, which reads a serialized vector blob via read_input and commits a
// PR01 summary via write_output (both supplied by ziskos).

#![no_main]
ziskos::entrypoint!(main);

extern "C" {
    fn monad_zkvm_run_precompile_tests();
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
    unsafe { monad_zkvm_run_precompile_tests() };
}
