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

use std::path::PathBuf;

fn main() {
    // Build the C++ guest archive and link it (plus program/main.c) against the
    // vendored SP1 SDK in ../sdk into the guest ELF. Surface its path to the
    // host driver via GUEST_ELF (embedded by include_bytes! in src/main.rs).
    let manifest = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let sdk_dir = manifest.parent().unwrap().join("sdk"); // zkvm/sp1/sdk
    let elf = monad_zkvm_build_support::Backend::Sp1.build_guest_elf(&sdk_dir);
    println!("cargo:rustc-env=GUEST_ELF={}", elf.display());
}
