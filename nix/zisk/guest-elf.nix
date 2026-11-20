# Reference guest from a clean commit and pinned toolchains.
# The ELF embeds the commit and Nix output name; the adjacent manifest
# records the source, toolchains, Cargo dependencies and ELF hash.
{
  stdenv,
  callPackage,
  python3,
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
    cargoRoot
    cargoDeps
    ;
  env = buildEnv.env // {
    MONAD_ZKVM_CMAKE_ARGS = "-DMONAD_ZKVM_NO_MERGE_CONSTRAINTS=ON -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DMONAD_ZKVM_NO_DIRTY_ACCOUNTS=ON -DMONAD_ZKVM_VARCODE_CACHE=ON -DMONAD_ZKVM_WIDE_MEMORY_SIZE=ON -DMONAD_ZKVM_KECCAKF_MEMO=ON";
  };
  strictDeps = true;
  # Preserve the guest ELF exactly as linked.
  dontUseCmakeConfigure = true;
  dontStrip = true;
  dontPatchELF = true;

  # The build directory reaches the ELF through panic locations and
  # Cargo's crate metadata. Only the sandbox fixes it, so refuse to build
  # anywhere else rather than produce a different ELF.
  preBuild = ''
    if [ "$NIX_BUILD_TOP" != /build ]; then
      echo "The reference guest must be built in the Nix sandbox:" \
        "the build directory is $NIX_BUILD_TOP, not /build." \
        "Pass --option sandbox true --option sandbox-fallback false." >&2
      exit 1
    fi
  '';

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
    # Record build inputs, the embedded output name and the ELF hash.
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

  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    ${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-strings -a "$out/monad-zkvm-zisk" |
      grep -Fx "monad-zkvm;commit=${rev};build=''${out##*/}" > /dev/null || {
        echo "Guest ELF does not contain the expected build identity" >&2
        exit 1
      }
    # Manual interpreter jumps must restore the native frame before dispatch.
    ${python3}/bin/python3 - ${src}/nix/check-zisk.py \
      "$out/monad-zkvm-zisk" \
      ${riscv64-none-elf-toolchain}/bin/riscv64-none-elf- \
      "$out/monad-zkvm-zisk.build.json" <<'PYTHON'
import json
import runpy
import subprocess
import sys
from pathlib import Path
checker, elf, prefix, manifest = sys.argv[1:]
checks = runpy.run_path(checker)
symbols = subprocess.check_output([prefix + "nm", "--print-size", "--defined-only", elf], text=True)
disassembly = subprocess.check_output([prefix + "objdump", "-d", elf], text=True)
count = checks["check_hand_made_jumps"](
    disassembly, checks["manual_jump_addresses"](symbols), checks["parse_function_sizes"](symbols))
path = Path(manifest)
data = json.loads(path.read_text())
data["interpreter_manual_jumps"] = count
path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
PYTHON
    runHook postInstallCheck
  '';
})
