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

// OpenVM entry for the witness-execution guest. Mirrors the ZisK entry
// (zkvm/zisk/src/main.rs), but where ziskos supplies the whole eth-act
// runtime ABI, here the runtime and accel modules provide it over OpenVM
// primitives — OpenVM has no eth-act runtime library.

#![no_main]
#![no_std]

extern crate alloc;

openvm::entry!(main);

// Moduli/curve setup for the algebra/ECC/pairing extensions declared in
// openvm.toml — without it the accelerated k256/pairing ops have no configured
// modulus to work against. Expands to an include of the sibling
// openvm_init.rs, which `cargo openvm build` regenerates from openvm.toml on
// every build and which is committed (as upstream does for its own guests) so
// that a plain `cargo build` and rust-analyzer also resolve it.
openvm::init!();

mod accel;
mod bls12_map;
mod runtime;

extern "C" {
    fn monad_zkvm_execute_witness();
}

fn main() {
    // The C++ archive's static ctors; OpenVM's entry doesn't run .init_array.
    runtime::run_init_array();
    unsafe { monad_zkvm_execute_witness() };
}
