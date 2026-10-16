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

# Shared tool and environment configuration for reference and development builds.
{ pkgs, callPackage, riscv64-none-elf-toolchain, zisk-rust-toolchain }:
let
  toolchainEnv = riscv64-none-elf-toolchain;
  ziskRustToolchain = zisk-rust-toolchain;
  ziskLinkerScript = callPackage ./zisk-linker-script.nix {
    lockFile = ../zkvm/zisk/Cargo.lock;
  };
  bin = "${toolchainEnv}/bin";
in
{
  nativeBuildInputs = [ zisk-rust-toolchain ziskLinkerScript pkgs.cmake pkgs.python3 ];
  buildInputs = [ pkgs.boost ];
  hardeningDisable = [ "all" ];
  env = {
    RISCV_TOOLCHAIN_DIR = toolchainEnv;
    RUSTC = "${ziskRustToolchain}/bin/rustc";
    CMAKE_PREFIX_PATH = "${pkgs.boost.dev}";
    CMAKE_GENERATOR = "Unix Makefiles";
    # zisk-zkvm-interface generates its bindings with bindgen, which parses
    # the headers with libclang for the guest target. Only libclang's own
    # headers may be on that path: nixpkgs's bindgen hook would add the host
    # glibc, whose stubs reject a non-x86 target.
    LIBCLANG_PATH = "${pkgs.lib.getLib pkgs.libclang}/lib";
    # Native Cargo dependencies also need the RISC-V compiler.
    CC_riscv64ima_zisk_zkvm_elf = "${bin}/riscv64-none-elf-gcc";
    CXX_riscv64ima_zisk_zkvm_elf = "${bin}/riscv64-none-elf-g++";
    MONAD_ZKVM_ZISK_DMA = "ON";
    MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES = "ON";
    ZISK_ROOT_CRATE = "monad_zkvm_zisk";
  };

  setup = ''
    # Bindgen needs freestanding headers; host flags must not reach RISC-V GCC.
    export BINDGEN_EXTRA_CLANG_ARGS="-ffreestanding $(< ${pkgs.llvmPackages.clang}/nix-support/cc-cflags)"
    unset CFLAGS CXXFLAGS CPPFLAGS LDFLAGS
  '';
  inherit ziskLinkerScript;
}
