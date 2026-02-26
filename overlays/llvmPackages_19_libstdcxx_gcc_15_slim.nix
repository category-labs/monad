# Overlay: install LLVM/Clang static archives (.a) into the dev output
# instead of the lib output, eliminating ~1 GB from runtime closures.
#
# The default nixpkgs LLVM build places both .so and .a files in the lib
# output, which ends up in every downstream package's runtime closure.
# Since clang links against libLLVM.so at runtime, the .a files are only
# needed at build time.
#
# This overlay patches cmake's install() directives to use a separate
# CMAKE_INSTALL_STATIC_LIBDIR variable for ARCHIVE DESTINATION, pointing
# it at the dev output.  The cmake-generated export files automatically
# get the correct absolute paths, and llvm-config is patched to emit
# both -L paths in --ldflags.
#
# Applies on top of nixpkgs' existing gnu-install-dirs.patch.
# Requires a from-source rebuild of LLVM and Clang.
#
# See: https://github.com/NixOS/nixpkgs/issues/230616
#      https://github.com/NixOS/nixpkgs/pull/162607 (prior attempt, reverted)

final: prev:
let
  inherit (prev) lib;
  origLlvmPkgs = prev.llvmPackages_19;

  llvmPatch = ./patches/llvm-separate-static-libdir.patch;
  pollyPatch = ./patches/polly-separate-static-libdir.patch;
  clangPatch = ./patches/clang-separate-static-libdir.patch;

  leanLibllvm = origLlvmPkgs.libllvm.overrideAttrs (old: {
    patches = (old.patches or []) ++ [ llvmPatch pollyPatch ];
    cmakeFlags = (old.cmakeFlags or []) ++ [
      (lib.cmakeFeature "CMAKE_INSTALL_STATIC_LIBDIR" "${placeholder "dev"}/lib")
    ];
  });

  leanLibclang = (origLlvmPkgs.libclang.override {
    libllvm = leanLibllvm;
  }).overrideAttrs (old: {
    patches = (old.patches or []) ++ [ clangPatch ];
    cmakeFlags = (old.cmakeFlags or []) ++ [
      (lib.cmakeFeature "CMAKE_INSTALL_STATIC_LIBDIR" "${placeholder "dev"}/lib")
    ];
  });

  clangMajor = lib.versions.major leanLibclang.version;

  origCC = origLlvmPkgs.stdenv.cc;

  # origCC.override { cc = … } replaces the unwrapped compiler but does
  # NOT re-evaluate extraBuildCommands, which is a pre-computed string
  # containing the original clang-lib store path.  The resource-root/include
  # symlink therefore still points at the old (fat) clang lib output.
  # Fix it up in postFixup.
  leanCC = (origCC.override { cc = leanLibclang; gccForLibs = final.gcc15.cc; }).overrideAttrs (old: {
    postFixup = (old.postFixup or "") + ''
      if [ -L "$out/resource-root/include" ]; then
        rm "$out/resource-root/include"
        ln -s "${leanLibclang.lib}/lib/clang/${clangMajor}/include" "$out/resource-root/include"
      fi
    '';
  });

in {
  llvmPackages_19_libstdcxx_gcc_15_slim = origLlvmPkgs // {
    libllvm = leanLibllvm;
    llvm = leanLibllvm;
    libclang = leanLibclang;
    clang-unwrapped = leanLibclang;
    stdenv = origLlvmPkgs.stdenv // {
      cc = leanCC;
    };
  };
}
