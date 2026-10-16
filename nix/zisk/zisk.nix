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

# Pin the ZisK linker script and check Cargo uses the same release.
# The setup hook supplies cargo-zisk's target flags and cfg.
{
  lib,
  stdenv,
  fetchFromGitHub,
  writeText,
  lockFile,
}:

let
  version = "1.4.0-alpha";
  tag = "v${version}";
  rev = "64a1f1664184e76053686745d50c6b9aaa51b034";
  owner = "0xPolygonHermez";
  repo = "zisk";
  # Compatibility requirement for this release; update with the ZisK pin.
  toolchainMajor = 4;

  src = fetchFromGitHub {
    inherit owner repo rev;
    hash = "sha256-oC7uNR5QQN1V8recpGKJVOXU/atfqHVgZjrQwxigheg=";
  };

  ziskos =
    lib.findFirst (p: p.name == "ziskos") (throw "ziskos is missing from ${toString lockFile}")
      (builtins.fromTOML (builtins.readFile lockFile)).package;
in
assert lib.assertMsg (
  ziskos.version == version
  && ziskos.source == "git+https://github.com/${owner}/${repo}.git?tag=${tag}#${rev}"
) "ZisK pins differ: update nix/zisk/zisk.nix and zkvm/zisk/Cargo.lock together.";
stdenv.mkDerivation {
  pname = "zisk-linker-script";
  version = builtins.substring 0 12 rev;

  dontUnpack = true;
  dontConfigure = true;
  dontBuild = true;

  installPhase = ''
    runHook preInstall
    install -Dm644 ${src}/ziskbuild/zisk_linker_script.ld $out/lib/zisk_linker_script.ld
    runHook postInstall
  '';

  setupHook = writeText "zisk-linker-script-setup-hook" ''
    # Match cargo-zisk 1.4 default Rust code generation.
    export CARGO_TARGET_RISCV64IMA_ZISK_ZKVM_ELF_RUSTFLAGS="-C target-feature=+unaligned-scalar-mem,+zba --cfg zisk_guest -C link-arg=-T@out@/lib/zisk_linker_script.ld"
  '';

  passthru = {
    inherit tag rev src toolchainMajor;
  };
}
