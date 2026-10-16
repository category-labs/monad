{
  description = "RISC-V toolchain and audited ZisK guest build";

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
          pkgs = import nixpkgs { inherit system; };
          ziskToolchain = import ./riscv64-toolchain.nix {
            inherit nixpkgs system;
            zisk = true;
          };
          # Git flakes must include submodules (see README.md). Exclude build
          # outputs and local Cargo settings from the immutable source input.
          src = pkgs.lib.cleanSourceWith {
            src = ../.;
            filter = path: type:
              let
                relative = pkgs.lib.removePrefix (toString ../. + "/") path;
                parts = pkgs.lib.splitString "/" relative;
              in
              builtins.elem (builtins.head parts)
                [ "category" "cmake" "zkvm" "third_party" "nix" ]
              && !(builtins.any (part: builtins.elem part
                [ ".git" ".cargo" "target" "__pycache__" ]) parts)
              && !(builtins.any (part: builtins.elem part
                [ "ethereum-tests" "execution-specs" "monad-execution-specs" ]) parts);
          };
        in
        {
          inherit (toolchain) cc bintools toolchainEnv;
          default = toolchain.toolchainEnv;
          zisk-toolchain = ziskToolchain.toolchainEnv;
          zisk = import ./zisk.nix {
            inherit pkgs src;
            toolchain = ziskToolchain;
            revision = self.rev or (throw
              "The audited ZisK build requires a clean Git flake with submodules; see nix/README.md");
          };
        });
    };
}
