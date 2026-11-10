# The reference ("official") ZisK guest: the witness-execution ELF built from
# a clean source commit with the patched cross GCC, the pinned ZisK Rust
# toolchain and explicit compiler options.
#
# Everything that determines the ELF is an input of this derivation, so its
# store path identifies the build. build.json beside the ELF records the
# same inputs for readers without nix.
{
  stdenv,
  callPackage,
  writeText,
  src,
  rev,
  riscv64-none-elf-toolchain,
  zisk-rust-toolchain,
}:

let
  target = "riscv64ima-zisk-zkvm-elf";

  buildEnv = callPackage ./zisk-build-env.nix {
    inherit rev;
    vendorCargoDeps = true;
  };
  inherit (buildEnv) zisk;

in
stdenv.mkDerivation (finalAttrs: {
  pname = "monad-zkvm-zisk";
  version = builtins.substring 0 12 rev;
  inherit src;

  inherit (buildEnv)
    nativeBuildInputs
    buildInputs
    hardeningDisable
    cargoRoot
    cargoDeps
    ;
  env = buildEnv.env // {
    MONAD_ZKVM_CMAKE_ARGS = "-DMONAD_ZKVM_KECCAKF_MEMO=ON";
  };
  strictDeps = true;
  # Preserve the guest ELF exactly as linked.
  dontUseCmakeConfigure = true;
  dontStrip = true;
  dontPatchELF = true;

  buildPhase = ''
    runHook preBuild
    python3 ${./check-zisk.py} --repo .
    cd zkvm/zisk
    export CARGO_HOME=$TMPDIR/cargo
    export CARGO_BUILD_JOBS=$NIX_BUILD_CORES NUM_JOBS=$NIX_BUILD_CORES
    export MONAD_ZKVM_BUILD_ID=''${out##*/}
    ${zisk-rust-toolchain}/bin/cargo build --release --frozen --target ${target} --target-dir target/elf --bin monad-zkvm-zisk
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
      --binutils-prefix ${riscv64-none-elf-toolchain}/bin/riscv64-none-elf- \
      --inputs ${
        writeText "zisk-inputs.json" (
          builtins.toJSON {
            commit = rev;
            source = toString src;
            riscv_toolchain = toString riscv64-none-elf-toolchain;
            rust_toolchain = toString zisk-rust-toolchain;
            cargo_dependencies = toString finalAttrs.cargoDeps;
            zisk = zisk.rev;
          }
        )
      } --build-id "''${out##*/}" --manifest $out/monad-zkvm-zisk.build.json
    runHook postInstallCheck
  '';
})
