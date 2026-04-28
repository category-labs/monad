let
  lock = builtins.fromJSON (builtins.readFile ./flake.lock);
  spec = lock.nodes.nixpkgs.locked;
  nixpkgs = fetchTarball "https://github.com/${spec.owner}/${spec.repo}/archive/${spec.rev}.tar.gz";
in
import nixpkgs