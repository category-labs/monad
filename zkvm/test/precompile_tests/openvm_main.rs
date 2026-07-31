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

// OpenVM entry for the precompile golden-vector test guest. Mirrors the
// witness entry (zkvm/openvm/src/main.rs) but hands control to the
// precompile-test C++ entry, which reads a serialized vector blob via
// read_input and commits a PR01 summary via write_output. This is the
// OpenVM bring-up target: it exercises every accelerator shim in accel.rs
// without involving the witness parser, trie, or EVM.

#![no_main]
#![no_std]

extern crate alloc;

openvm::entry!(main);

openvm::init!();

// All three are siblings, including `bls12_map`, which is only used by
// `accel`. A `#[path]` module resolves its own children relative to the
// directory holding the file it points at, so `accel` would look for a child
// next to itself here and inside `src/accel/` in the witness bin — the two
// bins cannot agree on one location. Declaring it flat sidesteps that.
#[path = "../../openvm/src/accel.rs"]
mod accel;
#[path = "../../openvm/src/bls12_map.rs"]
mod bls12_map;
#[path = "../../openvm/src/runtime.rs"]
mod runtime;

extern "C" {
    fn monad_zkvm_run_precompile_tests();
}

fn main() {
    runtime::run_init_array();
    unsafe { monad_zkvm_run_precompile_tests() };
}
