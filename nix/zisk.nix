{ pkgs, toolchain, src, revision }:
let
  requiredSubmodules = [
    "blst/bindings/blst.h" "cthash/CMakeLists.txt"
    "ethash/include/ethash/keccak.h" "evmc/include/evmc/evmc.h"
    "immer/CMakeLists.txt" "intx/include/intx/intx.hpp"
    "komihash/komihash.h" "nlohmann_json/include/nlohmann/json_fwd.hpp"
    "unordered_dense/CMakeLists.txt"
    "zkevm-standards/standards/io-interface/zkvm_io.h"
  ];
  sdk = import ./zisk-sdk.nix { inherit pkgs; };
  cargoDeps = pkgs.rustPlatform.importCargoLock {
    lockFile = ../zkvm/zisk/Cargo.lock;
    outputHashes = {
      "ziskos-1.3.2-alpha" = "sha256-697gSFxn30jL/+4cbJXObPNXvK32QVWYWE4I2GqYe8s=";
      "kzg-rs-0.2.8" = "sha256-YFkDQ9lKREHr+nzk3FuMtZrgpWDTEkqNe8KoA2kQFCg=";
    };
  };
  inputs = pkgs.writeText "zisk-inputs.json" (builtins.toJSON {
    inherit revision;
    source = toString src;
    gcc = toString toolchain.toolchainEnv;
    rust = toString sdk.rust;
    cargoZisk = toString sdk.cli;
    cargoDependencies = toString cargoDeps;
    boost = toString pkgs.boost.dev;
    libclang = toString pkgs.llvmPackages.libclang.lib;
  });
in
assert pkgs.lib.assertMsg
  (builtins.all (path: builtins.pathExists "${src}/third_party/${path}") requiredSubmodules)
  "ZisK sources are missing submodules: use the Git flake URL with submodules=1";
pkgs.stdenv.mkDerivation {
  pname = "monad-zisk-guest";
  version = builtins.substring 0 12 revision;
  inherit src;
  nativeBuildInputs = [
    pkgs.cmake pkgs.gnumake pkgs.python3 pkgs.rustup
    pkgs.rustPlatform.bindgenHook
    sdk.cli
  ];
  strictDeps = true;
  dontConfigure = true;
  dontStrip = true;
  dontPatchELF = true;
  # These are guest objects, not binaries for Nix's host platform.
  hardeningDisable = [ "all" ];

  RISCV_TOOLCHAIN_DIR = toolchain.toolchainEnv;
  CMAKE_PREFIX_PATH = "${pkgs.boost.dev}";
  CMAKE_GENERATOR = "Unix Makefiles";
  MONAD_ZKVM_OFFICIAL_PROFILE = "ON";
  MONAD_ZKVM_GIT_COMMIT = revision;
  CARGO_NET_OFFLINE = "true";

  buildPhase = ''
    runHook preBuild
    export CARGO_HOME=$TMPDIR/cargo RUSTUP_HOME=$TMPDIR/rustup
    mkdir -p "$CARGO_HOME" "$RUSTUP_HOME"
    rustup toolchain link zisk ${sdk.rust}
    rustup default zisk
    sed 's|directory = "cargo-vendor-dir"|directory = "${cargoDeps}"|' \
      ${cargoDeps}/.cargo/config.toml > "$CARGO_HOME/config.toml"
    export NUM_JOBS=$NIX_BUILD_CORES CARGO_BUILD_JOBS=$NIX_BUILD_CORES
    # bindgen reads freestanding guest headers, not the host libc.
    export BINDGEN_EXTRA_CLANG_ARGS="-ffreestanding $(< ${pkgs.llvmPackages.clang}/nix-support/cc-cflags)"
    # stdenv's host flags must not enter the RISC-V compilation.
    unset CFLAGS CXXFLAGS CPPFLAGS LDFLAGS
    export CC_riscv64ima_zisk_zkvm_elf=$RISCV_TOOLCHAIN_DIR/bin/riscv64-none-elf-gcc
    export CXX_riscv64ima_zisk_zkvm_elf=$RISCV_TOOLCHAIN_DIR/bin/riscv64-none-elf-g++
    cp zkvm/zisk/Cargo.lock "$TMPDIR/Cargo.lock.before"
    (cd zkvm/zisk && cargo-zisk build --release)
    cmp "$TMPDIR/Cargo.lock.before" zkvm/zisk/Cargo.lock
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out/share/monad-zisk
    elf=$out/bin/monad-zkvm-zisk
    install -Dm755 zkvm/zisk/target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk "$elf"
    cp ${./flake.lock} $out/share/monad-zisk/flake.lock
    cp zkvm/zisk/Cargo.lock $out/share/monad-zisk/Cargo.lock
    cp zkvm/zisk/target/guest-build/*/build/monad-zkvm-official-profile.json \
      $out/share/monad-zisk/
    cp ${inputs} $out/share/monad-zisk/inputs.json
    runHook postInstall
  '';

  postFixup = ''
    python3 zkvm/zisk/audit-official-build.py \
      --elf "$out/bin/monad-zkvm-zisk" --repo "$PWD" --source-commit ${revision} \
      --build-root zkvm/zisk/target/guest-build \
      --cargo-zisk ${sdk.cli}/bin/cargo-zisk \
      --manifest "$out/bin/monad-zkvm-zisk.build.json"
  '';

  passthru = { inherit cargoDeps sdk toolchain; };
  meta.platforms = [ "x86_64-linux" ];
}
