let
  lock = builtins.fromJSON (builtins.readFile ./flake.lock);
  spec = lock.nodes.nixpkgs.locked;
  nixpkgs = fetchTarball "https://github.com/${spec.owner}/${spec.repo}/archive/${spec.rev}.tar.gz";
  defaultOverlays = [
    (import ./overlays/llvmPackages_19_libstdcxx_gcc_15_slim.nix)
  ];
in
args: import nixpkgs (args // {
  overlays = defaultOverlays ++ (args.overlays or []);
})