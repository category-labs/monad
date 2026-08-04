# RISC-V cross compiler (GCC 15) with soft-float newlib.
#
# Produces a riscv64-none-elf toolchain targeting rv64ima / lp64 (no FPU).
# Newlib is shipped unmodified; zkvm/guest/CMakeLists.txt extracts only the
# objects it needs (setjmp/longjmp) by querying -print-file-name=libc.a.
{ nixpkgs, system }:

let
  # The stock pkgsCross.riscv64-embedded target is lp64d (double-float),
  # which the zkVM's bare-metal, no-FPU environment cannot use. Declaring
  # the cross system explicitly also rebuilds newlib for that ABI, so the
  # libc.a the guest build extracts from is soft-float too.
  pkgs = import nixpkgs {
    localSystem = system;
    crossSystem = {
      config = "riscv64-none-elf";
      libc = "newlib";
      gcc = {
        arch = "rv64ima";
        abi = "lp64";
      };
    };
  };

  # buildPackages is the build -> target package set, i.e. the cross
  # compiler itself. gcc15 is the wrapped compiler, which knows where the
  # target's newlib headers and libc.a live; gcc15.cc is the bare one,
  # which does not.
  cc = pkgs.buildPackages.gcc15;
  bintools = pkgs.buildPackages.binutils;

  # Symlink farm providing a stable <prefix>/bin layout, so the tree can be
  # handed to cmake as -DRISCV_TOOLCHAIN_DIR without callers having to know
  # the hash-named store paths.
  toolchainEnv = pkgs.buildPackages.buildEnv {
    name = "riscv64-none-elf-toolchain";
    paths = [ cc bintools ];
  };
in
{
  inherit cc bintools toolchainEnv;
}
