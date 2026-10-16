{
  description = "Toolchains for the monad zkVM guest build";

  # Pinned to a release branch: nixos-26.05 ships GCC 15.2.0, matching both
  # the Ubuntu host gcc-15 and the GCC that riscv-gnu-toolchain 2026.05.06
  # used to build. flake.lock pins the exact revision; bumping it rebuilds
  # the toolchain, so check the GCC version still matches (see README.md).
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";

  outputs = { self, nixpkgs }:
    let
      inherit (nixpkgs) lib;
      systems = [ "x86_64-linux" ];
      forAllSystems = lib.genAttrs systems;

    in
    {
      overlays.default = import ./overlay.nix;

      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };
        in
        {
          inherit (pkgs) riscv64-none-elf-toolchain zisk-rust-toolchain;
          default = pkgs.riscv64-none-elf-toolchain;
        });
    };
}
