# RISC-V cross compiler (GCC 15) with soft-float newlib and the ZisK
# backend patches.
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

  # The ZisK guest relies on -mzisk-dma and -mzisk-clean-byte-stores, which
  # exist only in the patched compiler; zkvm/toolchain/zisk-dma-gcc/README.md
  # describes the patches. Applied in order after nixpkgs's own GCC patches.
  ziskPatchDir = ../zkvm/toolchain/zisk-dma-gcc;
  ziskPatches = map (name: ziskPatchDir + "/${name}") [
    "0001-riscv-zisk-dma-lowering.patch"
    "0002-riscv.md-forward-port-15.2.0.diff"
    "0003-riscv-zisk-clean-byte-stores-15.2.0.diff"
  ];

  # buildPackages is the build -> target package set, i.e. the cross
  # compiler itself. gcc15 is the wrapped compiler, which knows where the
  # target's newlib headers and libc.a live; gcc15.cc is the bare one,
  # which does not. Patch the bare compiler and wrap it again the way
  # nixpkgs wraps gcc15, so the wrapper keeps that knowledge.
  cc = pkgs.buildPackages.wrapCC (
    pkgs.buildPackages.gcc15.cc.overrideAttrs (old: {
      patches = old.patches ++ ziskPatches;
    })
  );
  bintools = pkgs.buildPackages.binutils;

  # Symlink farm providing a stable <prefix>/bin layout, so the tree can be
  # handed to cmake as -DRISCV_TOOLCHAIN_DIR without callers having to know
  # the hash-named store paths.
  toolchainEnv = pkgs.buildPackages.buildEnv {
    name = "riscv64-none-elf-toolchain";
    paths = [ cc bintools ];

    # Check that each patched option changes the generated code, not only
    # that it parses: a compiler accepting -mzisk-dma while still emitting
    # memcpy calls would build a slower guest without any error. These are
    # the assumptions the guest's official profile is built on.
    postBuild = ''
      gcc=$out/bin/riscv64-none-elf-gcc
      flags="-O2 -march=rv64ima_zicsr -mabi=lp64 -mcmodel=medany"
      probe=$(mktemp -d)

      cat > "$probe/dma.c" <<'PROBE'
      void *memcpy(void *, void const *, unsigned long);
      void sink(void *);
      void p(char *d, char const *s) { memcpy(d, s, 512); sink(d); }
      PROBE
      $gcc $flags -mzisk-dma -S -o "$probe/dma.s" "$probe/dma.c"
      if ! grep -Eq 'csrs?[[:space:]]+.*0x813' "$probe/dma.s"; then
        cat "$probe/dma.s"
        echo "-mzisk-dma emits no DMA marker for a block memcpy" >&2
        exit 1
      fi

      cat > "$probe/byte.c" <<'PROBE'
      void f(unsigned char *p) { *p = 0xb8; }
      void g(unsigned char *p, unsigned char n) { *p = 0x80 + n; }
      PROBE
      $gcc $flags -mzisk-clean-byte-stores -S -o "$probe/byte.s" "$probe/byte.c"
      if ! grep -Eq 'li[[:space:]]+[a-z0-9]+,184$' "$probe/byte.s" ||
         ! grep -Eq 'addi[[:space:]]+[a-z0-9]+,[a-z0-9]+,128$' "$probe/byte.s"; then
        cat "$probe/byte.s"
        echo "-mzisk-clean-byte-stores leaves a byte store's source sign-extended" >&2
        exit 1
      fi

      rm -r "$probe"
    '';
  };
in
{
  inherit cc bintools toolchainEnv;
}
