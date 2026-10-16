# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# The packages this repository adds to nixpkgs: the toolchains the ZisK
# guest is built with. The flake applies it and also exports it, so other
# flakes can take the toolchains from an ordinary package set.
final: prev: {
  riscv64-none-elf-toolchain = final.callPackage ./riscv64-none-elf-toolchain.nix { };
  zisk-rust-toolchain = final.callPackage ./zisk-rust-toolchain.nix { };
}
