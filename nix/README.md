# zkVM toolchains and guest

Builds the `riscv64-none-elf` GCC used to cross-compile the zkVM guest
(`zkvm/guest`), with the ZisK backend patches from
`zkvm/toolchain/zisk-dma-gcc` applied, the Rust toolchain that links the
ZisK guest, and the reference ZisK guest ELF itself. CI consumes the GCC
from `docker/Dockerfile`; the same outputs work locally.

Flakes are not enabled in a stock Nix install. Either add

```
experimental-features = nix-command flakes
```

to `~/.config/nix/nix.conf`, or pass
`--extra-experimental-features "nix-command flakes"` to each `nix` command
below, as `docker/Dockerfile` does.

```shell
nix build ./nix#toolchainEnv
cmake -B build-zkvm -S zkvm/guest \
    -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf.cmake \
    -DRISCV_TOOLCHAIN_DIR=$PWD/result \
    -DCMAKE_BUILD_TYPE=Release
```

The flake lives in `nix/` but reads the GCC patches from
`zkvm/toolchain/zisk-dma-gcc`, so it must be evaluated from a tree that
holds both: the repository itself, or a copy of the two directories built
as `path:<copy>?dir=nix#toolchainEnv`, as `docker/Dockerfile` does.

## ZisK patches

The ZisK guest is compiled with `-mzisk-dma` and
`-mzisk-clean-byte-stores`, options added by the patches. After the symlink
farm is assembled, `riscv64-toolchain.nix` compiles two probes and requires
the code each option is meant to produce (`csrs 0x813` for a block
`memcpy`; `li ...,184` and `addi ...,...,128` for a byte constant and a byte
addition), so an unpatched or mis-patched compiler fails to build rather
than quietly building a slower guest.

## ZisK Rust toolchain

`zisk-rust-toolchain` is the compiler that builds `ziskos` and the guest's
Rust entry point: 0xPolygonHermez's rustc fork with the
`riscv64ima-zisk-zkvm-elf` target. `cargo-zisk toolchain install` fetches
the same prebuilt archive but takes the newest `zisk-4.x.y` release at
install time, so two machines can hold different compilers without any
record of it. `zisk-rust-toolchain.nix` pins the release tag and the
archive hash and relinks the binaries for nix. To bump it, change `tag`
and replace the hash with the one the first build reports.

```shell
nix build ./nix#zisk-rust-toolchain
./result/bin/rustc --version
```

## ZisK guest ELF

`zisk-elf` builds the reference ("official") guest, the ELF that published
benchmarks and releases must come from. Its inputs are all fixed by this
flake: the patched cross GCC above, the ZisK Rust toolchain
(`zisk-rust-toolchain`, the prebuilt `zisk-4.0.0` release of
0xPolygonHermez/rust, relinked for nix), the ZisK revision that
`zkvm/zisk/Cargo.lock` pins, the source commit, and the submodules the
guest reads at the revisions the commit pins. Build it from a clean
checkout:

```shell
nix build ./nix#zisk-elf
ls result/   # monad-zkvm-zisk, monad-zkvm-zisk.build.json
```

The ELF embeds `monad-zkvm-official;commit=<sha>`; `build.json` records
the ELF hash with the store paths of both toolchains, the ZisK revision and
the submodule revisions. Keep it with published benchmarks. A dirty tree
has no commit to record, so the build refuses it.

nix exports a git tree without its submodules, and asking for them would
pull in every nested test-vector repository. `guest-submodules.json`
therefore pins the URL and revision of each submodule the guest reads, and
`zisk-elf.nix` fetches those itself. `guest-submodules.py` regenerates the
file from `.gitmodules` and the gitlinks of `HEAD`; run it after bumping
one of those submodules. CI runs it with `--check`, so a stale file fails
the ZK workflow rather than building the wrong sources.

Before the ELF is kept, the derivation checks what the guest's official
profile assumes about it: the commit marker, the Zba/Zbb/Zbs/Zbkb ISA
attributes, and that every `operator delete` or `free` symbol that survived
linking is the bare return `nodelete.hpp` promises GCC.

`nix build --rebuild ./nix#zisk-elf` builds the ELF again and fails if the
result differs, so reproducibility is checked rather than assumed.

Development builds keep using `cargo-zisk build` with
`RISCV_TOOLCHAIN_DIR` pointing at `result` of `toolchainEnv`; they carry a
`monad-zkvm-dev` marker instead of a commit. To bump the Rust toolchain,
change `tag` in `zisk-rust-toolchain.nix` and replace the hash with the one
the first build reports.

## Why nix

`riscv-gnu-toolchain` builds by cloning binutils, gdb and newlib from
sourceware.org, which rate limits (HTTP 429) and has made cold builds fail
outright. nixpkgs fetches hash-pinned source tarballs from its own CDN
instead, so a cold build depends only on `cache.nixos.org`.

A cold build takes roughly 8 minutes on 16 cores. Only stage-1 GCC, newlib
and the final (patched) GCC are compiled; everything else, cross binutils
included, is substituted from `cache.nixos.org`. That is cheap enough that
no additional binary cache is needed — the docker layer cache absorbs the
common case, and a miss costs minutes rather than the tens of minutes a
full `riscv-gnu-toolchain` bootstrap would.

## Pinning

`flake.lock` pins nixpkgs. The pin is chosen so GCC is **15.2.0**, matching
both the Ubuntu host `gcc-15` and the GCC that `riscv-gnu-toolchain`
2026.05.06 built. Keeping the cross and host compilers in lockstep is
deliberate; check it after bumping:

```shell
nix build ./nix#toolchainEnv
./result/bin/riscv64-none-elf-gcc -dumpfullversion   # must match gcc-15 -dumpfullversion
nix flake update --flake ./nix                       # to bump
```

## Soft float

The stock `pkgsCross.riscv64-embedded` target is `lp64d` (hard float), which
the zkVM's no-FPU environment cannot use. `riscv64-toolchain.nix` declares
`rv64ima` / `lp64` explicitly so newlib is rebuilt for that ABI too. Verify
with:

```shell
./result/bin/riscv64-none-elf-readelf -h <obj> | grep Flags   # 0x0, not 0x4
```
