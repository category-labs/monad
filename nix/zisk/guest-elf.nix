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

  buildEnv = callPackage ./build-env.nix {
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
    env
    cargoRoot
    cargoDeps
    ;
  strictDeps = true;
  # Preserve the guest ELF exactly as linked.
  dontUseCmakeConfigure = true;
  dontStrip = true;
  dontPatchELF = true;

  buildPhase = ''
    runHook preBuild
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
    # The manifest: every input of the build, the build id (this store
    # path, which the ELF also embeds) and the hash of the ELF itself.
    substitute ${
      writeText "monad-zkvm-zisk.build.json" (
        builtins.toJSON {
          commit = rev;
          source = toString src;
          riscv_toolchain = toString riscv64-none-elf-toolchain;
          rust_toolchain = toString zisk-rust-toolchain;
          cargo_dependencies = toString finalAttrs.cargoDeps;
          zisk = zisk.rev;
          build = "@build@";
          elf_sha256 = "@elf_sha256@";
        }
      )
    } $out/monad-zkvm-zisk.build.json \
      --subst-var-by build "''${out##*/}" \
      --subst-var-by elf_sha256 "$(sha256sum "$elf" | cut -d' ' -f1)"
    runHook postInstall
  '';
})
