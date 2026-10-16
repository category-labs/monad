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

# Incremental guest builds in the working tree, including uncommitted changes.
{ pkgs, callPackage }:
let
  buildEnv = callPackage ./zisk-build-env.nix { inherit pkgs; };
in
pkgs.mkShell {
  inherit (buildEnv) nativeBuildInputs buildInputs hardeningDisable env;
  packages = [ pkgs.gitMinimal ];
  shellHook = buildEnv.setup + ''
    # Global Rust flags override the target-specific ZisK cfg and linker script.
    unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS CARGO_BUILD_RUSTFLAGS
    # Development builds must not inherit a reference build's identity.
    unset MONAD_ZKVM_GIT_COMMIT MONAD_ZKVM_BUILD_ID
  '';
}
