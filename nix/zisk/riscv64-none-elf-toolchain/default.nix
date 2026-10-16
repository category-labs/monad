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

# GCC 15 with ZisK DMA lowering and unmodified newlib for rv64ima/lp64.
{
  lib,
  path,
  stdenv,
  buildEnv,
  fetchurl,
}:

let
  # Override pkgsCross.riscv64-embedded's hard-float ABI so both GCC
  # and newlib use lp64. `path` selects the same pinned nixpkgs.
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

  hostGccMajor = (import ../../toolchain-env.nix { inherit lib; }).GCC_VERSION;

  ziskDmaPatch = fetchurl {
    url = "https://raw.githubusercontent.com/0xPolygonHermez/ziskethone/8bede62c7c9e843d1c2163eb05c56794ce706552/cpp-guest/patches/gcc/gcc-15.2.0/0001-riscv-zisk-dma-lowering.patch";
    hash = "sha256-nbjLPySX/x5ZymCTuNLIqoegkmSKe7jjyAGzqBMthPk=";
  };

  # Patch the cross compiler, then restore the nixpkgs wrapper that
  # locates the target's newlib headers and libraries.
  cc = pkgs.buildPackages.wrapCC (
    pkgs.buildPackages.gcc15.cc.overrideAttrs (old: {
      patches = old.patches ++ [ ziskDmaPatch ];
    })
  );
in

assert cc.version == "15.2.0";
assert lib.assertMsg (lib.versions.major cc.version == hostGccMajor)
  "riscv64-none-elf GCC ${cc.version} is not the GCC ${hostGccMajor} pinned in scripts/ubuntu-build/toolchain.env";
buildEnv {
  name = "riscv64-none-elf-toolchain";
  paths = [
    cc
    pkgs.buildPackages.binutils
  ];

  # Check that the patched option changes the generated code.
  postBuild = ''
    $out/bin/riscv64-none-elf-gcc -O2 -march=rv64ima_zicsr -mabi=lp64 \
      -mcmodel=medany -mzisk-dma -S -o probe-dma.s ${./probe-dma.c}
    if ! grep -Eq 'csrs?[[:space:]]+.*0x813' probe-dma.s; then
      cat probe-dma.s
      echo "-mzisk-dma emits no DMA marker for a block memcpy" >&2
      exit 1
    fi
  '';
}
