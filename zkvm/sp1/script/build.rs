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
    // Build the C++ guest archive and link it (plus the entry main.c) against
    // libzkevm.a — built from source from the SP1 zkEVM SDK — into the guest
    // ELF, and surface its path to the host driver via MONAD_ELF (embedded by
    // include_bytes! in src/main.rs). The `precompile-test` feature swaps the
    // witness executor for the precompile golden-vector test guest; both share
    // the guest archive + libzkevm.a and differ only in their entry main.c.
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_PRECOMPILE_TEST");
    let backend = monad_zkvm_build_support::Backend::Sp1;
    let elf = if std::env::var_os("CARGO_FEATURE_PRECOMPILE_TEST").is_some() {
        backend.build_precompile_test_elf()
    } else {
        backend.build_guest_elf()
    };
    println!("cargo:rustc-env=MONAD_ELF={}", elf.display());
}
