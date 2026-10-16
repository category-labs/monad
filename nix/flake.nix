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

      # The trees the guest build reads, without the test-vector submodules:
      # they hold gigabytes the guest never touches. The flake must be
      # fetched with ?submodules=1 for the remaining submodules to be present;
      # without it, the excluded paths do not exist at all.
      guestSource = lib.fileset.toSource {
        root = ../.;
        fileset = lib.fileset.difference
          (lib.fileset.unions [ ../zkvm ../category ../cmake ../third_party ../nix ])
          (lib.fileset.unions (map lib.fileset.maybeMissing [
            ../third_party/ethereum-tests
            ../third_party/execution-specs
            ../third_party/monad-execution-specs
          ]));
      };
    in
    {
      overlays.default = import ./overlay.nix;

      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ self.overlays.default ];
          };
          zisk = pkgs.callPackage ./zisk-dev-shell.nix { inherit pkgs; };
        in
        { inherit zisk; default = zisk; });

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
          # The reference guest ELF, from a clean checkout with submodules:
          #   nix build './nix?submodules=1#zisk-elf'
          zisk-elf = pkgs.callPackage ./zisk-elf.nix {
            inherit pkgs;
            src = guestSource;
            rev = self.rev or (throw
              "zisk-elf identifies the guest by its commit: commit or stash local changes first");
          };
        });
    };
}
