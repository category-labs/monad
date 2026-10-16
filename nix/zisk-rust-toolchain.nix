# The Rust toolchain ZisK programs are built with: a rustc fork from
# 0xPolygonHermez/rust adding the riscv64ima-zisk-zkvm-elf target, with
# ZisK's LLVM DMA lowering and a std built for it.
#
# cargo-zisk's `toolchain install` downloads the same archive, taking the
# newest zisk-4.x.y tag at install time. Here the tag and the archive hash
# are fixed, so the compiler that builds ziskos and the guest's Rust entry
# is part of the guest build's identity. The archive is a rustup-style
# toolchain tree (bin/, lib/rustlib/<target>/) linked against a glibc host;
# autoPatchelf relinks it against nix's glibc, libstdc++ and zlib.
{ pkgs }:

let
  tag = "zisk-4.0.0";
  host = "x86_64-unknown-linux-gnu";
in
pkgs.stdenv.mkDerivation {
  pname = "zisk-rust-toolchain";
  version = pkgs.lib.removePrefix "zisk-" tag;

  src = pkgs.fetchurl {
    url = "https://github.com/0xPolygonHermez/rust/releases/download/${tag}/rust-toolchain-${host}.tar.gz";
    hash = "sha256-xMRLVhLdAl9jDC+YSuX4qGK4hcSxS/xXyYDrgHO4z2I=";
  };
  # The archive unpacks bin/ and lib/ directly, with no top-level directory.
  sourceRoot = ".";

  nativeBuildInputs = [ pkgs.autoPatchelfHook ];
  buildInputs = [
    pkgs.stdenv.cc.cc.lib
    pkgs.zlib
  ];

  dontConfigure = true;
  dontBuild = true;

  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r bin lib $out/
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
