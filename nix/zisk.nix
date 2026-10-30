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

# The ZisK release the guest is built against, and what `cargo-zisk build`
# would add to every guest build from it: the zisk_guest cfg and the
# release's linker script. The guest names a ZisK version in one place
# only, the ziskos entry of its Cargo.lock, so everything taken from the
# release follows that pin and cannot drift from the runtime the guest
# links against. As a native build input, the package's setup hook adds
# the cfg and the script to cargo's rustflags for the ZisK target.
{
  lib,
  stdenv,
  writeText,
  lockFile,
}:

let
  ziskos =
    lib.findFirst (p: p.name == "ziskos") (throw "ziskos is missing from ${toString lockFile}")
      (builtins.fromTOML (builtins.readFile lockFile)).package;
  # "git+<url>?tag=<tag>#<rev>"
  source = builtins.match "git\\+([^?]*)\\?tag=([^#]*)#([0-9a-f]*)" ziskos.source;
  tag = builtins.elemAt source 1;
  rev = builtins.elemAt source 2;
  src = builtins.fetchGit {
    url = builtins.elemAt source 0;
    ref = "refs/tags/${tag}";
    inherit rev;
  };

  # The only statement ZisK makes about which Rust toolchain it needs:
  # `cargo-zisk toolchain install` downloads the newest zisk-<major>.x.y
  # release of 0xPolygonHermez/rust for this major.
  support = builtins.readFile "${src}/cli/src/commands/user/toolchain/support.rs";
  major = builtins.match ".*const TOOLCHAIN_MAJOR: u64 = ([0-9]+);.*" support;
in
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
    inherit tag rev src;
    toolchainMajor =
      if major == null then
        throw "ZisK ${tag} no longer defines TOOLCHAIN_MAJOR in cli/src/commands/user/toolchain/support.rs"
      else
        lib.toInt (builtins.head major);
  };
}
