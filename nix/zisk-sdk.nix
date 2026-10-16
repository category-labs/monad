# Host tools from versioned upstream releases; never consult ziskup's latest.
{ pkgs }:
let
  # The released CLI links libsodium.so.23; nixpkgs' newer ABI is .26.
  libsodium23 = pkgs.libsodium.overrideAttrs {
    version = "1.0.18";
    src = pkgs.fetchurl {
      url = "https://download.libsodium.org/libsodium/releases/libsodium-1.0.18.tar.gz";
      hash = "sha256-b1BEkLNCpPikxKAvybhmy++GItXfTlRStGvhIeRmNsE=";
    };
  };
  unpack = { pname, version, url, hash, installPhase, runtimeLibraries ? [ ] }:
    pkgs.stdenvNoCC.mkDerivation {
      inherit pname version installPhase;
      src = pkgs.fetchurl { inherit url hash; };
      sourceRoot = ".";
      SOURCE_DATE_EPOCH = 1;
      nativeBuildInputs = [ pkgs.autoPatchelfHook ];
      buildInputs = [
        pkgs.stdenv.cc.cc.lib pkgs.zlib pkgs.zstd pkgs.openssl
        pkgs.gmp pkgs.libffi
      ] ++ runtimeLibraries;
      dontStrip = true;
      # Only patch host executables; guest libraries must stay untouched.
      dontAutoPatchelf = true;
      dontPatchELF = true;
      strictDeps = true;
    };
in
{
  rust = unpack {
    pname = "zisk-rust";
    version = "4.0.0";
    url = "https://github.com/0xPolygonHermez/rust/releases/download/zisk-4.0.0/rust-toolchain-x86_64-unknown-linux-gnu.tar.gz";
    hash = "sha256-xMRLVhLdAl9jDC+YSuX4qGK4hcSxS/xXyYDrgHO4z2I=";
    installPhase = ''
      mkdir -p $out
      cp -r bin lib $out/
      autoPatchelf $out/bin $out/lib/*.so* $out/lib/rustlib/x86_64-unknown-linux-gnu
      $out/bin/rustc --print target-list | grep -Fx riscv64ima-zisk-zkvm-elf
      $out/bin/cargo --version
    '';
  };
  cli = unpack {
    pname = "cargo-zisk";
    version = "1.3.2-alpha";
    url = "https://github.com/0xPolygonHermez/zisk/releases/download/v1.3.2-alpha/cargo_zisk_linux_amd64.tar.gz";
    hash = "sha256-q7d5Qn9saSTHSC+UM1b2DGV3SZQyu4Bq80lmmypym9c=";
    runtimeLibraries = [ libsodium23 pkgs.openmpi ];
    installPhase = ''
      mkdir -p $out/bin
      install -m755 bin/cargo-zisk-cpu $out/bin/cargo-zisk
      autoPatchelf $out/bin
      $out/bin/cargo-zisk --version | grep -F 'cargo-zisk 1.3.2-alpha '
    '';
  };
}
