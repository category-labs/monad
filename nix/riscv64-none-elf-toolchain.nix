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
  fetchFromGitHub,
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

  # GCC 15.2.0 with the two opt-in ZisK backend changes. Keep the revision
  # and content hash pinned; compiler implementation changes live in the fork.
  ziskGccSource = fetchFromGitHub {
    owner = "anne-laure-s";
    repo = "gcc";
    rev = "93353bc300d688e7a929d4bfb2768e3465289e34";
    hash = "sha256-0fXyEdpaCOhBHBLjtRtRRHvKG+YFajXOXNrmHpFNJ6M=";
  };

  ziskProbes = lib.fileset.toSource {
    root = ./gcc-probes;
    fileset = lib.fileset.fileFilter (
      file: file.hasExt "sh" || file.hasExt "c"
    ) ./gcc-probes;
  };

  # buildPackages is the build -> target package set, i.e. the cross
  # compiler itself. gcc15 is the wrapped compiler, which knows where the
  # target's newlib headers and libc.a live; gcc15.cc is the bare one,
  # which does not. Replace the bare compiler source and wrap it again the way
  # nixpkgs wraps gcc15, so the wrapper keeps that knowledge.
  cc = pkgs.buildPackages.wrapCC (
    pkgs.buildPackages.gcc15.cc.overrideAttrs (old: {
      src = ziskGccSource;
      # Git sources omit generated parsers shipped in GCC release tarballs.
      nativeBuildInputs = old.nativeBuildInputs ++ [
        pkgs.buildPackages.flex
        pkgs.buildPackages.bison
      ];
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
  # and the check remain here as the guest's toolchain contract.
  postBuild = ''
    bash ${ziskProbes}/check-probes.sh $out/bin/riscv64-none-elf-gcc
  '';
}
