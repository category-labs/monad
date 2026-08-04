{
  description = "RISC-V cross toolchain for the monad zkVM guest build";

  # Pinned to a release branch: nixos-26.05 ships GCC 15.2.0, matching both
  # the Ubuntu host gcc-15 and the GCC that riscv-gnu-toolchain 2026.05.06
  # used to build. flake.lock pins the exact revision; bumping it rebuilds
  # the toolchain, so check the GCC version still matches (see README.md).
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      packages = forAllSystems (system:
        let
          toolchain = import ./riscv64-toolchain.nix { inherit nixpkgs system; };
        in
        {
          inherit (toolchain) cc bintools toolchainEnv;
          default = toolchain.toolchainEnv;
        });
    };
}
