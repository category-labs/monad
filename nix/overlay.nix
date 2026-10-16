# The packages this repository adds to nixpkgs: the toolchains the ZisK
# guest is built with. The flake applies it and also exports it, so other
# flakes can take the toolchains from an ordinary package set.
final: prev: {
  riscv64-none-elf-toolchain = final.callPackage ./riscv64-none-elf-toolchain.nix { };
  zisk-rust-toolchain = final.callPackage ./zisk-rust-toolchain.nix { };
}
