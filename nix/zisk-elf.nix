# The reference ("official") ZisK guest: the witness-execution ELF built from
# a clean source commit with the patched cross GCC, the pinned ZisK Rust
# toolchain and explicit compiler options.
#
# Everything that determines the ELF is an input of this derivation, so its
# store path identifies the build. build.json beside the ELF records the
# same inputs for readers without nix.
{
  pkgs,
  callPackage,
  src,
  rev,
  riscv64-none-elf-toolchain,
  zisk-rust-toolchain
}:

let
  inherit (pkgs) lib;
  target = "riscv64ima-zisk-zkvm-elf";
  lockFile = ../zkvm/zisk/Cargo.lock;

  toolchainEnv = riscv64-none-elf-toolchain;
  ziskRustToolchain = zisk-rust-toolchain;
  ziskLinkerScript = callPackage ./zisk-linker-script.nix { inherit lockFile; };
  bin = "${toolchainEnv}/bin";

in
pkgs.stdenv.mkDerivation (finalAttrs: {
  pname = "monad-zkvm-zisk";
  version = builtins.substring 0 12 rev;
  inherit src;

  cargoRoot = "zkvm/zisk";
  cargoDeps = pkgs.rustPlatform.importCargoLock {
    inherit lockFile;
    outputHashes = {
      "ziskos-1.3.2-alpha" = "sha256-697gSFxn30jL/+4cbJXObPNXvK32QVWYWE4I2GqYe8s=";
      "kzg-rs-0.2.8" = "sha256-YFkDQ9lKREHr+nzk3FuMtZrgpWDTEkqNe8KoA2kQFCg=";
    };
  };

  nativeBuildInputs = [
    pkgs.rustPlatform.cargoSetupHook
    zisk-rust-toolchain
    ziskLinkerScript
    pkgs.cmake
    pkgs.python3
  ];
  # Boost.Outcome headers, found through CMAKE_PREFIX_PATH.
  buildInputs = [ pkgs.boost ];
  strictDeps = true;
  hardeningDisable = [ "all" ];
  # Cargo drives the guest's CMake project through zkvm/build-support.
  dontUseCmakeConfigure = true;
  # The guest ELF is the artifact; leave it exactly as linked.
  dontStrip = true;
  dontPatchELF = true;

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
    MONAD_ZKVM_CMAKE_ARGS = "-DMONAD_ZKVM_KECCAKF_MEMO=ON";
    ZISK_ROOT_CRATE = "monad_zkvm_zisk";
    MONAD_ZKVM_GIT_COMMIT = rev;
  };

  buildPhase = ''
    runHook preBuild
    python3 ${./check-zisk.py} --repo .
    cd zkvm/zisk
    export CARGO_HOME=$TMPDIR/cargo
    export CARGO_BUILD_JOBS=$NIX_BUILD_CORES NUM_JOBS=$NIX_BUILD_CORES
    # Use Clang's freestanding headers rather than host glibc.
    export BINDGEN_EXTRA_CLANG_ARGS="-ffreestanding $(< ${pkgs.llvmPackages.clang}/nix-support/cc-cflags)"
    # Host stdenv flags must not reach the RISC-V compiler.
    unset CFLAGS CXXFLAGS CPPFLAGS LDFLAGS
    export MONAD_ZKVM_BUILD_ID=''${out##*/}
    ${ziskRustToolchain}/bin/cargo build --release --frozen --target ${target} --target-dir target/elf --bin monad-zkvm-zisk
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    elf=target/elf/${target}/release/monad-zkvm-zisk
    install -Dm644 "$elf" $out/monad-zkvm-zisk
    runHook postInstall
  '';

  # Validate the source assumptions and linked artifact.
  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    elf=$out/monad-zkvm-zisk

    python3 ${./check-zisk.py} --repo ../.. --elf "$elf" \
      --binutils-prefix ${bin}/riscv64-none-elf- \
      --inputs ${pkgs.writeText "zisk-inputs.json" (builtins.toJSON {
        commit = rev;
        source = toString src;
        riscv_toolchain = toString toolchainEnv;
        rust_toolchain = toString ziskRustToolchain;
        cargo_dependencies = toString finalAttrs.cargoDeps;
        zisk = ziskLinkerScript.rev;
      })} --build-id "''${out##*/}" --manifest $out/monad-zkvm-zisk.build.json
    runHook postInstallCheck
  '';
})
