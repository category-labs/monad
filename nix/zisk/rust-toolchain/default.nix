# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Pin ZisK's rustc fork and target libraries by release and archive hash.
# autoPatchelf adapts the host binaries to Nix while leaving RISC-V
# libraries unchanged.
{
  lib,
  stdenv,
  fetchurl,
  autoPatchelfHook,
  zlib,
  zstd,
  openssl,
  gmp,
  libffi,
}:

let
  # build-env.nix checks this major against the pinned ZisK release.
  tag = "zisk-4.1.0";
  host = "x86_64-unknown-linux-gnu";
in
stdenv.mkDerivation {
  pname = "zisk-rust-toolchain";
  version = lib.removePrefix "zisk-" tag;

  src = fetchurl {
    url = "https://github.com/0xPolygonHermez/rust/releases/download/${tag}/rust-toolchain-${host}.tar.gz";
    hash = "sha256-mpkhpVjKZS38RuUEOpKqcKjvjsG+G7sPPDkt18C1z+E=";
  };
  # The archive unpacks bin/ and lib/ directly, with no top-level directory.
  sourceRoot = ".";

  nativeBuildInputs = [ autoPatchelfHook ];
  buildInputs = [
    stdenv.cc.cc.lib
    zlib
    zstd
    openssl
    gmp
    libffi
  ];

  # Only patch host binaries, preserving RISC-V libraries.
  dontAutoPatchelf = true;
  dontPatchELF = true;
  dontStrip = true;
  strictDeps = true;
  dontConfigure = true;
  dontBuild = true;

  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r bin lib $out/
    autoPatchelf $out/bin $out/lib/*.so* $out/lib/rustlib/x86_64-unknown-linux-gnu
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
