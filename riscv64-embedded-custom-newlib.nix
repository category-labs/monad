# Custom RISC-V cross compiler with minimal newlib.
#
# Provides headers from newlib but strips out libc/libstdc++ compiled code,
# keeping only a small set of selected functions (longjmp, strcmp, memcpy, etc.).
#
# Evaluates directly to a wrapped GCC derivation for use with Bazel's
# nixpkgs_cc_configure (nix_file parameter). Other outputs are available
# via passthru attributes: customSpecs, minimalLibc, newlibHeaders.

let
  pkgs = import ./nixpkgs.nix {};

  # Selected functions to extract from newlib's libc.a.
  # Everything else (full libc/libstdc++ runtime) is stripped out.
  functions = {
    libc = [
      "setjmp" "longjmp"
      # "strcmp" "strncmp" "strlen" "strcpy" "strncpy" "strcat" "strncat"
      # "memcpy" "memmove" "memset" "memcmp" "memchr"
    ];
  };

  baseGcc = pkgs.pkgsCross.riscv64-embedded.buildPackages.gcc15;

  # Convert function names to object file names
  # "setjmp" -> "libc_a-setjmp.o"
  # "sin" in libm -> "libm_a-sin.o"
  toObjectName = lib: func:
    let prefix = if lib == "libc" then "libc_a-"
                 else if lib == "libm" then "libm_a-"
                 else throw "Unknown library: ${lib}. Use 'libc' or 'libm'";
    in "${prefix}${func}.o";

  allObjects = pkgs.lib.flatten (
    pkgs.lib.mapAttrsToList
      (lib: funcs: map (toObjectName lib) funcs)
      functions
  );

  # Extract selected objects from libc.a and create libc_minimal.a
  minimalLibc = pkgs.runCommand "newlib-minimal" {
    nativeBuildInputs = [ pkgs.pkgsCross.riscv64-embedded.buildPackages.binutils ];
  } ''
    mkdir -p $out/lib
    LIBC="${pkgs.pkgsCross.riscv64-embedded.stdenv.cc.libc}/riscv64-none-elf/lib/libc.a"

    cd $out/lib
    ${pkgs.lib.concatMapStringsSep "\n" (obj: ''
      riscv64-none-elf-ar x "$LIBC" ${obj} 2>/dev/null || echo "Warning: ${obj} not found" >&2
    '') allObjects}

    if [ -n "$(ls -A *.o 2>/dev/null)" ]; then
      riscv64-none-elf-ar rcs libc_minimal.a *.o
      rm *.o
    else
      # Create empty archive if no objects found
      touch empty.c
      ${baseGcc}/bin/riscv64-none-elf-gcc -c empty.c -o empty.o
      riscv64-none-elf-ar rcs libc_minimal.a empty.o
      rm empty.c empty.o
    fi

    # Document what's included
    echo "Selected functions:" > $out/lib/included.txt
    ${pkgs.lib.concatMapStringsSep "\n" (lib:
      pkgs.lib.concatMapStringsSep "\n" (func: ''
        echo "  ${lib}: ${func}" >> $out/lib/included.txt
      '') (functions.${lib} or [])
    ) (builtins.attrNames functions)}
  '';

  # Custom specs file that strips libc/libstdc++ linking, keeps headers + minimal functions
  customSpecs = pkgs.writeText "minimal-libc.specs" ''
    %rename link_gcc_c_sequence original_link_gcc_c_sequence

    *link_gcc_c_sequence:
    %(original_link_gcc_c_sequence) --start-group ${minimalLibc}/lib/libc_minimal.a --end-group

    *lib:

    *startfile:

    *endfile:

    *cc1:
    %(cc1_cpu)

    *cc1plus:
    -fno-exceptions -fno-rtti %(cc1_cpu)
  '';

  # Newlib headers (for reference / CMake builds)
  newlibHeaders = pkgs.runCommand "newlib-headers" {} ''
    mkdir -p $out/include
    cp -r ${pkgs.pkgsCross.riscv64-embedded.stdenv.cc.libc}/riscv64-none-elf/include/* $out/include/
  '';

  # Wrapped GCC that automatically uses our specs.
  # passthru attributes (targetPrefix, isClang) are required by
  # rules_nixpkgs cc.nix toolchain probing.
  prefix = baseGcc.targetPrefix or "riscv64-none-elf-";

  wrappedGcc = pkgs.symlinkJoin {
    name = "${prefix}gcc-wrapped";
    paths = [ baseGcc ];
    nativeBuildInputs = [ pkgs.makeWrapper ];
    passthru = {
      targetPrefix = prefix;
      isClang = false;
      inherit customSpecs minimalLibc newlibHeaders;
    };
    postBuild = ''
      wrapProgram $out/bin/${prefix}gcc \
        --add-flags "-specs=${customSpecs}"

      wrapProgram $out/bin/${prefix}g++ \
        --add-flags "-specs=${customSpecs}"

      # Recreate cc/c++ as symlinks to the wrapped gcc/g++ to avoid
      # double-wrapping (nixpkgs has cc -> gcc, c++ -> g++ as symlinks).
      rm -f $out/bin/${prefix}cc $out/bin/${prefix}c++
      ln -s ${prefix}gcc $out/bin/${prefix}cc
      ln -s ${prefix}g++ $out/bin/${prefix}c++
    '';
  };

in wrappedGcc
