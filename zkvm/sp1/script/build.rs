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
    let elf = monad_zkvm_build_support::Backend::Sp1.build_guest_elf();
    println!("cargo:rustc-env=GUEST_ELF={}", elf.display());
}
