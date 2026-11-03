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
    // Both entries link the shared C++ archive and libzkevm.a built from the
    // pinned SDK source. Export the selected ELF for src/main.rs to embed.
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_PRECOMPILE_TEST");
    let backend = monad_zkvm_build_support::Backend::Sp1;
    let elf = if std::env::var_os("CARGO_FEATURE_PRECOMPILE_TEST").is_some() {
        backend.build_precompile_test_elf()
    } else {
        backend.build_guest_elf()
    };
    println!("cargo:rustc-env=MONAD_ELF={}", elf.display());
}
