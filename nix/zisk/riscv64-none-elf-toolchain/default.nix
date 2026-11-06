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

# RISC-V cross compiler (GCC 15) with soft-float newlib and the ZisK
# backend patches.
#
# Produces a riscv64-none-elf toolchain targeting rv64ima / lp64 (no FPU).
# Newlib is shipped unmodified; zkvm/guest/CMakeLists.txt extracts only the
# objects it needs (setjmp/longjmp) by querying -print-file-name=libc.a.
{
  lib,
  path,
  stdenv,
  buildEnv,
  fetchurl,
}:

let
  # The stock pkgsCross.riscv64-embedded target is lp64d (double-float),
  # which the zkVM's bare-metal, no-FPU environment cannot use. Declaring
  # the cross system explicitly also rebuilds newlib for that ABI, so the
  # libc.a the guest build extracts from is soft-float too. `path` is the
  # nixpkgs this package set came from.
  pkgs = import path {
    localSystem = stdenv.hostPlatform.system;
    crossSystem = {
      config = "riscv64-none-elf";
      libc = "newlib";
      gcc = {
        arch = "rv64ima";
        abi = "lp64";
      };
    };
  };

  # The ZisK guest relies on -mzisk-dma and -mzisk-clean-byte-stores, which
  # exist only in the patched compiler; README.md beside this file describes
  # the patches. The DMA lowering patch is ZisK's own, taken from
  # the ziskethone C++ guest at a pinned commit; the clean-byte-stores patch
  # is vendored and applies on top of it. Both come after nixpkgs's own GCC
  # patches.
  ziskDmaPatch = fetchurl {
    url = "https://raw.githubusercontent.com/0xPolygonHermez/ziskethone/8bede62c7c9e843d1c2163eb05c56794ce706552/cpp-guest/patches/gcc/gcc-15.2.0/0001-riscv-zisk-dma-lowering.patch";
    hash = "sha256-nbjLPySX/x5ZymCTuNLIqoegkmSKe7jjyAGzqBMthPk=";
  };
  ziskPatches = [
    ziskDmaPatch
    ./patches/riscv-zisk-clean-byte-stores-15.2.0.diff
  ];

  ziskProbes = lib.fileset.toSource {
    root = ./tests;
    fileset = lib.fileset.fileFilter (
      file: file.hasExt "sh" || file.hasExt "c"
    ) ./tests;
  };

  # buildPackages is the build -> target package set, i.e. the cross
  # compiler itself. gcc15 is the wrapped compiler, which knows where the
  # target's newlib headers and libc.a live; gcc15.cc is the bare one,
  # which does not. Patch the bare compiler and wrap it again the way
  # nixpkgs wraps gcc15, so the wrapper keeps that knowledge.
  cc = pkgs.buildPackages.wrapCC (
    pkgs.buildPackages.gcc15.cc.overrideAttrs (old: {
      patches = old.patches ++ ziskPatches;
    })
  );
  bintools = pkgs.buildPackages.binutils;
in
# Symlink farm providing a stable <prefix>/bin layout, so the tree can be
# handed to cmake as -DRISCV_TOOLCHAIN_DIR without callers having to know
# the hash-named store paths.
assert cc.version == "15.2.0";
buildEnv {
  name = "riscv64-none-elf-toolchain";
  paths = [
    cc
    bintools
  ];

  # Check that each patched option changes the generated code, not only
  # that it parses: a compiler accepting -mzisk-dma while still emitting
  # memcpy calls would build a slower guest without any error. The probes
  # and the check live in tests/ beside this file.
  postBuild = ''
    bash ${ziskProbes}/check-probes.sh $out/bin/riscv64-none-elf-gcc
  '';
}
