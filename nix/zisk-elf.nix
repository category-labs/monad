# The reference ("official") ZisK guest: the witness-execution ELF built from
# a clean source commit with the patched cross GCC, the pinned ZisK Rust
# toolchain and the guest's official CMake profile.
#
# Everything that determines the ELF is an input of this derivation, so its
# store path identifies the build. build.json beside the ELF records the
# same inputs for readers without nix.
{
  pkgs,
  src,
  rev,
  toolchainEnv,
  ziskRustToolchain,
}:

let
  inherit (pkgs) lib;
  target = "riscv64ima-zisk-zkvm-elf";
  lockFile = ../zkvm/zisk/Cargo.lock;

  # ziskos pins the ZisK revision in Cargo.lock. The linker script that
  # cargo-zisk passes to every guest link comes from the same checkout.
  ziskos = lib.findFirst (p: p.name == "ziskos") (throw "ziskos is missing from zkvm/zisk/Cargo.lock") (
    builtins.fromTOML (builtins.readFile lockFile)
  ).package;
  ziskSource = builtins.match "git\\+([^?]*)\\?tag=([^#]*)#([0-9a-f]*)" ziskos.source;
  ziskUrl = builtins.elemAt ziskSource 0;
  ziskTag = builtins.elemAt ziskSource 1;
  ziskRev = builtins.elemAt ziskSource 2;
  zisk = builtins.fetchGit {
    url = ziskUrl;
    ref = "refs/tags/${ziskTag}";
    rev = ziskRev;
  };

  # nix exports the source tree without its submodules: asking for them
  # brings in every nested test-vector repository, which the guest never
  # reads. Fetch the ones it does read at the revisions guest-submodules.json
  # pins; guest-submodules.py regenerates that file from the gitlinks and
  # checks it in CI.
  submodules = lib.mapAttrs (
    path: pin:
    builtins.fetchGit {
      inherit (pin) url rev;
      allRefs = true;
    }
  ) (builtins.fromJSON (builtins.readFile ./guest-submodules.json));

  bin = "${toolchainEnv}/bin";
in
pkgs.stdenv.mkDerivation {
  pname = "monad-zkvm-zisk";
  version = builtins.substring 0 12 rev;
  inherit src;

  cargoRoot = "zkvm/zisk";
  cargoDeps = pkgs.rustPlatform.importCargoLock {
    inherit lockFile;
    # Git dependencies are fetched at their locked commits; no extra hashes.
    allowBuiltinFetchGit = true;
  };

  nativeBuildInputs = [
    pkgs.rustPlatform.cargoSetupHook
    ziskRustToolchain
    pkgs.cmake
  ];
  # Boost.Outcome headers, found through CMAKE_PREFIX_PATH.
  buildInputs = [ pkgs.boost ];
  # Cargo drives the guest's CMake project through zkvm/build-support.
  dontUseCmakeConfigure = true;
  # The guest ELF is the artifact; leave it exactly as linked.
  dontStrip = true;
  dontPatchELF = true;

  env = {
    RISCV_TOOLCHAIN_DIR = toolchainEnv;
    # zisk-zkvm-interface generates its bindings with bindgen, which parses
    # the headers with libclang for the guest target. Only libclang's own
    # headers may be on that path: nixpkgs's bindgen hook would add the host
    # glibc, whose stubs reject a non-x86 target.
    LIBCLANG_PATH = "${pkgs.lib.getLib pkgs.libclang}/lib";
    # The cmake crate asks cc-rs for the target's compiler and flags; name
    # it, as cc-rs would otherwise look for one named after the triple.
    CC_riscv64ima_zisk_zkvm_elf = "${bin}/riscv64-none-elf-gcc";
    CXX_riscv64ima_zisk_zkvm_elf = "${bin}/riscv64-none-elf-g++";
    MONAD_ZKVM_OFFICIAL_PROFILE = "ON";
    MONAD_ZKVM_GIT_COMMIT = rev;
    # What `cargo-zisk build` adds to `cargo build --target ${target}`.
    CARGO_TARGET_RISCV64IMA_ZISK_ZKVM_ELF_RUSTFLAGS = "--cfg zisk_guest -C link-arg=-T${zisk}/ziskbuild/zisk_linker_script.ld";
  };

  prePatch = lib.concatStrings (
    lib.mapAttrsToList (path: tree: ''
      rm -rf ${path}
      ln -s ${tree} ${path}
    '') submodules
  );

  buildPhase = ''
    runHook preBuild
    cd zkvm/zisk
    export CARGO_HOME=$TMPDIR/cargo
    # nix names the build directory randomly, and two things would carry it
    # into the ELF. Panic locations in the vendored crates name their source
    # files: remap the prefix. And cargo hashes the absolute path of the
    # build-support dependency, which lies outside the zkvm/zisk workspace,
    # into the root crate's -C metadata, which names that crate's codegen
    # unit in the symbol table: pin the root crate's metadata instead.
    cat > "$TMPDIR/rustc-wrapper" <<'EOF'
    #!/bin/sh
    root=0
    for a in "$@"; do
      [ "$a" = monad_zkvm_zisk ] && root=1
    done
    if [ $root = 1 ]; then
      n=$#
      while [ $n -gt 0 ]; do
        a=$1
        shift
        case "$a" in metadata=*) a=metadata=monad_zkvm_zisk ;; esac
        set -- "$@" "$a"
        n=$((n - 1))
      done
    fi
    exec "$@" --remap-path-prefix="$NIX_BUILD_TOP=/build"
    EOF
    chmod +x "$TMPDIR/rustc-wrapper"
    export RUSTC_WRAPPER=$TMPDIR/rustc-wrapper
    cargo build --release --offline --target ${target} --target-dir target/elf --bin monad-zkvm-zisk
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    elf=target/elf/${target}/release/monad-zkvm-zisk
    install -Dm644 "$elf" $out/monad-zkvm-zisk
    cat > $out/monad-zkvm-zisk.build.json <<EOF
    {
      "commit": "${rev}",
      "elf_sha256": "$(sha256sum "$elf" | cut -d ' ' -f 1)",
      "riscv_toolchain": "${toolchainEnv}",
      "rust_toolchain": "${ziskRustToolchain}",
      "zisk": "${ziskRev}",
      "submodules": ${builtins.toJSON (lib.mapAttrs (path: tree: tree.rev) submodules)}
    }
    EOF
    runHook postInstall
  '';

  # The assumptions the guest's official profile makes about the linked ELF.
  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    elf=$out/monad-zkvm-zisk

    # The ELF names the commit it was built from (zkvm/guest/execute_witness.cpp).
    grep -aq 'monad-zkvm-official;commit=${rev}' "$elf"

    # The ISA the guest is compiled for (zkvm/guest/CMakeLists.txt).
    attributes=$(${bin}/riscv64-none-elf-readelf -A "$elf")
    for extension in zba zbb zbs zbkb; do
      if ! grep -q "$extension" <<< "$attributes"; then
        echo "ELF attributes omit $extension" >&2
        exit 1
      fi
    done

    # nodelete.hpp declares delete and free no-ops for GCC to drop; any that
    # survive linking must be a bare return (4 bytes), or the attribute lied.
    ${bin}/riscv64-none-elf-nm --print-size --defined-only "$elf" |
      awk '($4 ~ /^_Zd[la]/ || $4 == "free") && strtonum("0x" $2) != 4 {
             print "nodelete.hpp asserts " $4 " is a no-op, but it is " strtonum("0x" $2) " bytes"
             bad = 1
           }
           END { exit bad }'
    runHook postInstallCheck
  '';
}
