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
  python3,
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
  # Vendor the Cargo dependencies from the lock file and make cargo use
  # them, for sandboxed builds. The development shell leaves this off:
  # the hook would copy the vendored tree into the working directory and
  # rewrite its cargo configuration.
  vendorCargoDeps ? false,
}:
let
  cargoRoot = "zkvm/zisk";
  lockFile = ../${cargoRoot}/Cargo.lock;
  ziskLinkerScript = callPackage ./zisk-linker-script.nix { inherit lockFile; };
  # bindgen generates Rust bindings from ZisK's C headers for RISC-V.
  # This hook tells it to use clang's built-in headers. The standard nixpkgs
  # hook also adds host glibc headers, which are incompatible with this target.
  # We use a hook rather than `env` because the flags must be read from a
  # file in clang's package during build setup.
  bindgenHook = makeSetupHook { name = "zisk-bindgen-hook"; } (
    writeText "zisk-bindgen-hook.sh" ''
      export BINDGEN_EXTRA_CLANG_ARGS="-ffreestanding $(< ${llvmPackages.clang}/nix-support/cc-cflags)"
    ''
  );
in
{
  nativeBuildInputs = lib.optional vendorCargoDeps rustPlatform.cargoSetupHook ++ [
    zisk-rust-toolchain
    ziskLinkerScript
    bindgenHook
    cmake
    python3
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
    # Native Cargo dependencies also need the RISC-V compiler.
    CC_riscv64ima_zisk_zkvm_elf = "${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-gcc";
    CXX_riscv64ima_zisk_zkvm_elf = "${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-g++";
    MONAD_ZKVM_ZISK_DMA = "ON";
    MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES = "ON";
    ZISK_ROOT_CRATE = "monad_zkvm_zisk";
  }
  // lib.optionalAttrs (rev != "") { MONAD_ZKVM_GIT_COMMIT = rev; };

  inherit ziskLinkerScript;
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
