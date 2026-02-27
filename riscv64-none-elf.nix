# RISC-V cross compiler (GCC 15) with soft-float newlib.
#
# Builds a riscv64-none-elf GCC 15 targeting rv64ima / lp64 (no FPU).
# Newlib headers and libc.a are included unmodified; the cmake build
# extracts only the objects it needs (setjmp/longjmp).

let
  nixpkgsImport = import ./nixpkgs.nix;

  # Cross system with soft-float ABI matching our zkVM targets (rv64ima / lp64).
  # The default riscv64-embedded uses lp64d (double-float) which is incompatible
  # with the bare-metal zkVM environment that has no FPU.
  softFloatCross = {
    config = "riscv64-none-elf";
    libc = "newlib";
    gcc = {
      arch = "rv64ima";
      abi = "lp64";
    };
  };

  softFloatPkgs = nixpkgsImport { crossSystem = softFloatCross; };

in softFloatPkgs.buildPackages.gcc15
