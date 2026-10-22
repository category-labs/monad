# The reference ZisK guest: the witness-execution ELF built from a clean
# source commit with the patched cross GCC, the pinned ZisK Rust toolchain,
# the linker script of the ZisK release Cargo.lock pins, and both
# patched-GCC options on.
#
# Everything that determines the ELF is an input of this derivation, so its
# store path identifies the build. build.json beside the ELF records the
# same inputs for readers without nix.
{
  lib,
  stdenv,
  callPackage,
  rustPlatform,
  cmake,
  boost,
  libclang,
  riscv64-none-elf-toolchain,
  zisk-rust-toolchain,
  src,
  rev,
}:

let
  target = "riscv64ima-zisk-zkvm-elf";
  lockFile = ../zkvm/zisk/Cargo.lock;
  ziskLinkerScript = callPackage ./zisk-linker-script.nix { inherit lockFile; };
in
stdenv.mkDerivation {
  pname = "monad-zkvm-zisk";
  version = builtins.substring 0 12 rev;
  inherit src;

  cargoRoot = "zkvm/zisk";
  cargoDeps = rustPlatform.importCargoLock {
    inherit lockFile;
    # Git dependencies are fetched at their locked commits; no extra hashes.
    allowBuiltinFetchGit = true;
  };

  nativeBuildInputs = [
    rustPlatform.cargoSetupHook
    zisk-rust-toolchain
    ziskLinkerScript
    cmake
  ];
  # Boost.Outcome headers, found through CMAKE_PREFIX_PATH.
  buildInputs = [ boost ];
  # Cargo drives the guest's CMake project through zkvm/build-support.
  dontUseCmakeConfigure = true;
  # The guest ELF is the artifact; leave it exactly as linked.
  dontStrip = true;
  dontPatchELF = true;

  env = {
    RISCV_TOOLCHAIN_DIR = riscv64-none-elf-toolchain;
    # zisk-zkvm-interface generates its bindings with bindgen, which parses
    # the headers with libclang for the guest target. Only libclang's own
    # headers may be on that path: nixpkgs's bindgen hook would add the host
    # glibc, whose stubs reject a non-x86 target.
    LIBCLANG_PATH = "${lib.getLib libclang}/lib";
    # The cmake crate asks cc-rs for the target's compiler and flags; name
    # it, as cc-rs would otherwise look for one named after the triple.
    CC_riscv64ima_zisk_zkvm_elf = "${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-gcc";
    CXX_riscv64ima_zisk_zkvm_elf = "${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-g++";
    # The guest settings the reference build enables; see zkvm/guest/CMakeLists.txt.
    MONAD_ZKVM_ZISK_DMA = "ON";
    MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES = "ON";
    MONAD_ZKVM_GIT_COMMIT = rev;
    # The toolchain's rustc wrapper keeps nix's randomly named build
    # directory out of the ELF; this names the crate whose metadata it pins.
    ZISK_ROOT_CRATE = "monad_zkvm_zisk";
  };

  buildPhase = ''
    runHook preBuild
    cd zkvm/zisk
    export CARGO_HOME=$TMPDIR/cargo
    # The output path names every input of this build, so the ELF carries
    # it beside the commit.
    export MONAD_ZKVM_BUILD_ID=''${out##*/}
    cargo build --release --offline --target ${target} --target-dir target/elf --bin monad-zkvm-zisk
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    elf=target/elf/${target}/release/monad-zkvm-zisk
    install -Dm644 "$elf" $out/monad-zkvm-zisk
    cat > $out/monad-zkvm-zisk.build.json <<EOF
    {
      "store": "$out",
      "commit": "${rev}",
      "elf_sha256": "$(sha256sum "$elf" | cut -d ' ' -f 1)",
      "riscv_toolchain": "${riscv64-none-elf-toolchain}",
      "rust_toolchain": "${zisk-rust-toolchain}",
      "zisk": "${ziskLinkerScript.rev}"
    }
    EOF
    runHook postInstall
  '';

  # What the guest build promises about the linked ELF.
  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    elf=$out/monad-zkvm-zisk

    # The ELF names the commit and the store path it was built from
    # (zkvm/guest/execute_witness.cpp).
    grep -aq "monad-zkvm;commit=${rev};build=''${out##*/}" "$elf"

    # The ISA the guest is compiled for (zkvm/guest/CMakeLists.txt).
    attributes=$(${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-readelf -A "$elf")
    for extension in zba zbb zbs zbkb; do
      if ! grep -q "$extension" <<< "$attributes"; then
        echo "ELF attributes omit $extension" >&2
        exit 1
      fi
    done

    # nodelete.hpp declares delete and free no-ops for GCC to drop; any that
    # survive linking must be a bare return (4 bytes), or the attribute lied.
    ${riscv64-none-elf-toolchain}/bin/riscv64-none-elf-nm --print-size --defined-only "$elf" |
      awk '($4 ~ /^_Zd[la]/ || $4 == "free") && strtonum("0x" $2) != 4 {
             print "nodelete.hpp asserts " $4 " is a no-op, but it is " strtonum("0x" $2) " bytes"
             bad = 1
           }
           END { exit bad }'
    runHook postInstallCheck
  '';
}
