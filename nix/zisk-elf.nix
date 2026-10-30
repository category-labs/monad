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
  target = "riscv64ima-zisk-zkvm-elf";
  lockFile = ../zkvm/zisk/Cargo.lock;

  toolchainEnv = riscv64-none-elf-toolchain;
  ziskRustToolchain = zisk-rust-toolchain;
  buildEnv = callPackage ./zisk-build-env.nix {
    inherit pkgs riscv64-none-elf-toolchain zisk-rust-toolchain;
  };
  inherit (buildEnv) ziskLinkerScript;
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
      "ziskos-1.4.0-alpha" = "sha256-oC7uNR5QQN1V8recpGKJVOXU/atfqHVgZjrQwxigheg=";
      "kzg-rs-0.2.8" = "sha256-YFkDQ9lKREHr+nzk3FuMtZrgpWDTEkqNe8KoA2kQFCg=";
    };
  };

  nativeBuildInputs = [ pkgs.rustPlatform.cargoSetupHook ] ++ buildEnv.nativeBuildInputs;
  inherit (buildEnv) buildInputs hardeningDisable;
  strictDeps = true;
  # Cargo drives CMake; preserve the guest ELF exactly as linked.
  dontUseCmakeConfigure = true;
  dontStrip = true;
  dontPatchELF = true;
  env = buildEnv.env // { MONAD_ZKVM_GIT_COMMIT = rev; };

  buildPhase = ''
    runHook preBuild
    python3 ${./check-zisk.py} --repo .
    cd zkvm/zisk
    export CARGO_HOME=$TMPDIR/cargo
    export CARGO_BUILD_JOBS=$NIX_BUILD_CORES NUM_JOBS=$NIX_BUILD_CORES
    ${buildEnv.setup}
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
