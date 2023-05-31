with (import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/refs/tags/23.05.tar.gz") { });
let llvm = llvmPackages_16;
in (mkShell.override { stdenv = overrideCC llvm.stdenv (llvm.clang.override { gccForLibs = gcc13.cc; }); }) {
  buildInputs = [
    gtest
    rocksdb
    cmake
    brotli
    abseil-cpp
    boost174
    zstd
    ninja
  ];

  shellHook = "export CXXFLAGS+=$NIX_CFLAGS_COMPILE";
  # https://discourse.nixos.org/t/how-to-get-c-headers-included-in-nix-cflags-compile/21638/2
  # https://discourse.nixos.org/t/gcc11stdenv-and-clang/17734
}
