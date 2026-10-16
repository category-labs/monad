# What `cargo-zisk build` adds to every guest build: the zisk_guest cfg
# and the linker script of its ZisK release. The script is taken from the
# release the guest's Cargo.lock pins ziskos to, the only place the guest
# names a ZisK version, so it cannot drift from the runtime the guest
# links against. As a native build input, the package's setup hook adds
# both to cargo's rustflags for the ZisK target.
{
  lib,
  stdenv,
  writeText,
  lockFile,
}:

let
  ziskos = lib.findFirst (p: p.name == "ziskos") (throw "ziskos is missing from ${toString lockFile}") (
    builtins.fromTOML (builtins.readFile lockFile)
  ).package;
  # "git+<url>?tag=<tag>#<rev>"
  source = builtins.match "git\\+([^?]*)\\?tag=([^#]*)#([0-9a-f]*)" ziskos.source;
  rev = builtins.elemAt source 2;
  zisk = builtins.fetchGit {
    url = builtins.elemAt source 0;
    ref = "refs/tags/${builtins.elemAt source 1}";
    inherit rev;
  };
in
stdenv.mkDerivation {
  pname = "zisk-linker-script";
  version = builtins.substring 0 12 rev;

  dontUnpack = true;
  dontConfigure = true;
  dontBuild = true;

  installPhase = ''
    runHook preInstall
    install -Dm644 ${zisk}/ziskbuild/zisk_linker_script.ld $out/lib/zisk_linker_script.ld
    runHook postInstall
  '';

  setupHook = writeText "zisk-linker-script-setup-hook" ''
    export CARGO_TARGET_RISCV64IMA_ZISK_ZKVM_ELF_RUSTFLAGS="--cfg zisk_guest -C link-arg=-T@out@/lib/zisk_linker_script.ld"
  '';

  passthru = {
    inherit rev;
  };
}
