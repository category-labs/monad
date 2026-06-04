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

fn main() {
    // Build the C++ guest archive and link it (plus program/main.c) against
    // libzkevm.a — built from source from the SP1 zkEVM SDK — into the guest
    // ELF. Surface its path to the host driver via GUEST_ELF (embedded by
    // include_bytes! in src/main.rs).
    let elf = monad_zkvm_build_support::Backend::Sp1.build_guest_elf();
    println!("cargo:rustc-env=GUEST_ELF={}", elf.display());
}
