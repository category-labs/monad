# The packages this repository adds to nixpkgs: the toolchain the ZisK
# guest is built with. The flake applies it and also exports it, so other
# flakes can take the toolchain from an ordinary package set.
final: prev: {
  riscv64-none-elf-toolchain = final.callPackage ./riscv64-none-elf-toolchain.nix { };
}
