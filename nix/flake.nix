{
  description = "Toolchains and the reference guest build for the monad zkVM";

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

      # The trees the guest build reads. Submodules are not part of this
      # export; zisk-elf.nix fetches the ones the guest needs.
      guestSource = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.unions [ ../zkvm ../category ../cmake ../third_party ];
      };
    in
    {
      packages = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
          toolchain = import ./riscv64-toolchain.nix { inherit nixpkgs system; };
          ziskRustToolchain = import ./zisk-rust-toolchain.nix { inherit pkgs; };
        in
        {
          inherit (toolchain) cc bintools toolchainEnv;
          default = toolchain.toolchainEnv;
          zisk-rust-toolchain = ziskRustToolchain;
          # The reference guest ELF, from a clean checkout:
          #   nix build ./nix#zisk-elf
          zisk-elf = import ./zisk-elf.nix {
            inherit pkgs ziskRustToolchain;
            inherit (toolchain) toolchainEnv;
            src = guestSource;
            rev = self.rev or (throw
              "zisk-elf identifies the guest by its commit: commit or stash local changes first");
          };
        });
    };
}
