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
{
  lib,
  callPackage,
  cmake,
  boost,
  libclang,
  llvmPackages,
  makeSetupHook,
  writeText,
  riscv64-none-elf-toolchain,
  rustPlatform,
  zisk-rust-toolchain,
  # Commit the build identifies itself with; empty for development builds.
  rev ? "",
  # Vendor locked dependencies for sandboxed builds. Leave this off in
  # the shell to avoid copying dependencies and rewriting Cargo config.
  vendorCargoDeps ? false,
}:
let
  cargoRoot = "zkvm/zisk";
  lockFile = ../../${cargoRoot}/Cargo.lock;
  zisk = callPackage ./zisk.nix { inherit lockFile; };
  # Use clang's built-in headers for RISC-V bindgen, without host glibc.
  # A setup hook reads the flags from clang's package at build time.
  bindgenHook = makeSetupHook { name = "zisk-bindgen-hook"; } (
    writeText "zisk-bindgen-hook.sh" ''
      export BINDGEN_EXTRA_CLANG_ARGS="-ffreestanding $(< ${llvmPackages.clang}/nix-support/cc-cflags)"
    ''
  );
  toolchainMajor = lib.toInt (lib.versions.major zisk-rust-toolchain.version);
in
# Check the Rust toolchain major required by the pinned ZisK release.
assert lib.assertMsg (toolchainMajor == zisk.toolchainMajor) ''
  zisk-rust-toolchain ${zisk-rust-toolchain.version} has major ${toString toolchainMajor},
  but ziskos ${zisk.tag} wants toolchain major ${toString zisk.toolchainMajor}.
  Update nix/zisk/rust-toolchain/default.nix and the compatibility requirement in nix/zisk/zisk.nix together.'';
{
  nativeBuildInputs = lib.optional vendorCargoDeps rustPlatform.cargoSetupHook ++ [
    zisk-rust-toolchain
    zisk
    bindgenHook
    cmake
  ];
  buildInputs = [ boost ];
  hardeningDisable = [ "all" ];
  env = {
    RISCV_TOOLCHAIN_DIR = riscv64-none-elf-toolchain;
    RUSTC = "${zisk-rust-toolchain}/bin/rustc";
    CMAKE_PREFIX_PATH = "${boost.dev}";
    CMAKE_GENERATOR = "Unix Makefiles";
    # The libclang library that bindgen uses to read the C headers.
    LIBCLANG_PATH = "${lib.getLib libclang}/lib";
    # C/C++ dependencies compiled by Cargo must target RISC-V.
    CC_riscv64ima_zisk_zkvm_elf = "${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-gcc";
    CXX_riscv64ima_zisk_zkvm_elf = "${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-g++";
    MONAD_ZKVM_ZISK_DMA = "ON";
  }
  // lib.optionalAttrs (rev != "") { MONAD_ZKVM_GIT_COMMIT = rev; };

  inherit zisk;
}
// lib.optionalAttrs vendorCargoDeps {
  inherit cargoRoot;
  cargoDeps = rustPlatform.importCargoLock {
    inherit lockFile;
    outputHashes = {
      "ziskos-1.4.0-alpha" = "sha256-oC7uNR5QQN1V8recpGKJVOXU/atfqHVgZjrQwxigheg=";
      "kzg-rs-0.2.8" = "sha256-YFkDQ9lKREHr+nzk3FuMtZrgpWDTEkqNe8KoA2kQFCg=";
    };
  };
}
