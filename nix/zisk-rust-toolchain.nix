# The Rust toolchain ZisK programs are built with: a rustc fork from
# 0xPolygonHermez/rust adding the riscv64ima-zisk-zkvm-elf target, with
# ZisK's LLVM DMA lowering and a std built for it.
#
# cargo-zisk's `toolchain install` downloads the same archive, taking the
# newest zisk-<major>.x.y tag at install time; the ZisK source names only
# that major (TOOLCHAIN_MAJOR in cli/src/commands/user/toolchain/support.rs),
# so the exact tag and the archive hash have to be fixed here. The
# compiler that builds ziskos and the guest's Rust entry is then part of
# the guest build's identity. The archive is a rustup-style toolchain
# tree (bin/, lib/rustlib/<target>/) linked against a glibc host;
# autoPatchelf relinks it against nix's glibc, libstdc++ and zlib.
{
  lib,
  stdenv,
  fetchurl,
  autoPatchelfHook,
  zlib,
  writeText,
}:

let
  tag = "zisk-4.0.0";
  host = "x86_64-unknown-linux-gnu";
in
stdenv.mkDerivation {
  pname = "zisk-rust-toolchain";
  version = lib.removePrefix "zisk-" tag;

  src = fetchurl {
    url = "https://github.com/0xPolygonHermez/rust/releases/download/${tag}/rust-toolchain-${host}.tar.gz";
    hash = "sha256-xMRLVhLdAl9jDC+YSuX4qGK4hcSxS/xXyYDrgHO4z2I=";
  };
  # The archive unpacks bin/ and lib/ directly, with no top-level directory.
  sourceRoot = ".";

  nativeBuildInputs = [ autoPatchelfHook ];
  buildInputs = [
    stdenv.cc.cc.lib
    zlib
  ];

  dontConfigure = true;
  dontBuild = true;

  # Every build with this toolchain among its native build inputs gets the
  # rustc wrapper; it does nothing outside a nix build (see the script).
  setupHook = writeText "zisk-rust-toolchain-setup-hook" ''
    export RUSTC_WRAPPER=@out@/bin/zisk-rustc-wrapper
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r bin lib $out/
    # For builds that must not depend on their build directory; see the script.
    install -m755 ${./zisk-rustc-wrapper.sh} $out/bin/zisk-rustc-wrapper
    runHook postInstall
  '';

  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    $out/bin/rustc --version
    $out/bin/cargo --version
    $out/bin/rustc --print target-list | grep -qx riscv64ima-zisk-zkvm-elf
    runHook postInstallCheck
  '';
}
