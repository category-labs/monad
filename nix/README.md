# zkVM toolchains and guest

Builds the `riscv64-none-elf` GCC used to cross-compile the zkVM guest
(`zkvm/guest`) from the pinned
[ZisK GCC fork](https://github.com/anne-laure-s/gcc/tree/zisk/gcc-15.2.0),
the Rust toolchain that links the ZisK guest, and the reference ZisK guest
ELF itself. CI consumes the GCC
from `docker/Dockerfile`; the same outputs work locally.

Flakes are not enabled in a stock Nix install. Either add

```
experimental-features = nix-command flakes
```

to `~/.config/nix/nix.conf`, or pass
`--extra-experimental-features "nix-command flakes"` to each `nix` command
below, as `docker/Dockerfile` does.

```shell
nix build .#riscv64-none-elf-toolchain
cmake -B build-zkvm -S zkvm/guest \
    -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf.cmake \
    -DRISCV_TOOLCHAIN_DIR=$PWD/result \
    -DCMAKE_BUILD_TYPE=Release
```

Both toolchains are ordinary packages added by `overlay.nix`, which the
flake exports as `overlays.default` for other package sets to apply.

The flake lives at the repository root and its packages and compiler probes
in `nix/`. A toolchain-only build needs `flake.nix`, `flake.lock` and `nix/`,
as copied by `docker/Dockerfile`.

## ZisK GCC dependency

`riscv64-none-elf-toolchain.nix` pins the fork by commit and source hash.
It is based on GCC 15.2.0 and adds two options, both disabled by default:

- `-mzisk-dma` lowers block memory operations to ZisK DMA markers.
- `-mzisk-clean-byte-stores` prefers zero-extended byte constants and additions.

The reference guest build explicitly enables both. Nix retains its own GCC
packaging patches, binutils and soft-float newlib; the ZisK backend changes
are maintained in the fork, not applied from this repository.

After building the toolchain, `gcc-probes/check-probes.sh` checks the generated
assembly for both options. This catches a compiler that accepts the flags
without emitting the expected instructions. To check an externally installed
compiler, run:

```sh
bash nix/gcc-probes/check-probes.sh /path/to/riscv64-none-elf-gcc
```

When updating the dependency, update both its revision and hash, then rebuild
the toolchain and guest. Do not infer ELF identity from a passing probe.

## ZisK Rust toolchain

`zisk-rust-toolchain` is the compiler that builds `ziskos` and the guest's
Rust entry point: 0xPolygonHermez's rustc fork with the
`riscv64ima-zisk-zkvm-elf` target. `cargo-zisk toolchain install` fetches
the same prebuilt archive but takes the newest `zisk-4.x.y` release at
install time, so two machines can hold different compilers without any
record of it. The ZisK source names only the major of the toolchain it
wants, so `zisk-rust-toolchain.nix` pins the release tag and the archive
hash itself and relinks the binaries for nix. To bump it, change `tag`
and replace the hash with the one the first build reports.

```shell
nix build .#zisk-rust-toolchain
./result/bin/rustc --version
```

The toolchain also installs `zisk-rustc-wrapper`, a `RUSTC_WRAPPER` for
builds that must not depend on their build directory, and its setup hook
exports `RUSTC_WRAPPER` into every build that lists the toolchain among
its native build inputs; the script explains what it rewrites and why.

## ZisK guest ELF

`zisk-elf` builds the reference guest, the ELF that published benchmarks
and releases must come from. Its inputs are all fixed by this
flake: the patched cross GCC above, the ZisK Rust toolchain, the linker
script `cargo-zisk` would supply, which `zisk-linker-script.nix` takes
from the ZisK release `zkvm/zisk/Cargo.lock` pins `ziskos` to and adds to
the guest's rustflags through its setup hook, and the source commit,
submodules included.
Build it from a clean checkout:

```shell
nix build '.?submodules=1#zisk-elf'
ls result/   # monad-zkvm-zisk, monad-zkvm-zisk.build.json
```

The ELF embeds `monad-zkvm;commit=<sha>;build=<store path>`, the store
path being its own, whose hash covers every input of the build;
`build.json` records the ELF hash with the store paths of both toolchains
and the ZisK revision. Keep it with published benchmarks. A dirty tree has
no commit to record, so the build refuses it.

`?submodules=1` makes nix read every submodule, nested ones included, from
the local checkout at the commit the tree records, so all of them must be
initialised (`git submodule update --init --recursive`). Only the trees the
guest reads are copied into the store; the test-vector submodules are left
out, so a build copies a few hundred megabytes rather than the whole tree.

Before the ELF is kept, the derivation checks what the guest build
promises about it: the commit marker, the Zba/Zbb/Zbs/Zbkb ISA attributes,
and that every `operator delete` or `free` symbol that survived linking is
the bare return `nodelete.hpp` promises GCC. The checks also inspect the
allocator source definitions, including functions removed by optimization,
and verify the actual return instruction encoding.

`nix build --rebuild '.?submodules=1#zisk-elf'` builds the ELF again and fails if the
result differs. Run it to check reproducibility rather than assuming it.

## Development shell

On x86_64 Linux, enter the pinned development environment from the repository
root, then build the working tree directly with Cargo:

```shell
git submodule update --init --recursive
nix develop .#zisk
cd zkvm/zisk
cargo build --release --locked --target riscv64ima-zisk-zkvm-elf --target-dir target/elf --bin monad-zkvm-zisk
```

The ELF is `target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk`.
Local edits are supported, and Cargo/CMake keep their incremental artifacts.
`cargo-zisk` is not needed for this path. Cargo builds the C++ archive through
`build.rs`.

Use `nix develop`, rather than plain `nix shell`: the environment needs setup
hooks for the Rust wrapper, the linker script and the bindgen flags, plus
cross-compiler settings. `zisk-build-env.nix` shares these settings with the
reference build, including explicit DMA and clean byte stores. The shell clears
inherited host compiler flags and global Rust flags so they cannot reach the
RISC-V compiler or override the target-specific ZisK cfg and linker script.
This shell does not require a
clean source commit or run the reference ELF audit; its default marker is
`monad-zkvm;commit=none;build=none`.

The shell supplies build tools, not `ziskemu` or the prover. Cargo may download
locked dependencies on its first run. macOS users need an x86_64 Linux machine
or VM for this shell; locally installed toolchains remain supported through
`RISCV_TOOLCHAIN_DIR` (see `zkvm/README.md`).

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

The root `flake.lock` pins nixpkgs. The pin is chosen so GCC is **15.2.0**, matching
both the Ubuntu host `gcc-15` and the GCC that `riscv-gnu-toolchain`
2026.05.06 built. Keeping the cross and host compilers in lockstep is
deliberate; check it after bumping:

```shell
nix build .#riscv64-none-elf-toolchain
./result/bin/riscv64-none-elf-gcc -dumpfullversion   # must match gcc-15 -dumpfullversion
nix flake update                                     # to bump
```

## Soft float

The stock `pkgsCross.riscv64-embedded` target is `lp64d` (hard float), which
the zkVM's no-FPU environment cannot use. `riscv64-none-elf-toolchain.nix` declares
`rv64ima` / `lp64` explicitly so newlib is rebuilt for that ABI too. Verify
with:

```shell
./result/bin/riscv64-none-elf-readelf -h <obj> | grep Flags   # 0x0, not 0x4
```

The Nix recipe needs an x86_64 Linux builder, including when run from macOS.
Local development remains available with locally installed tools. The
unordered_dense fork remains pinned by the repository's gitlink and
`.gitmodules`.

Benchmark drivers invoking Cargo directly must pass
`MONAD_ZKVM_ZISK_DMA=ON` and `MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES=ON`.
`MONAD_ZKVM_OFFICIAL_PROFILE` is no longer used. The commit and build stamps
are supplied separately with `MONAD_ZKVM_GIT_COMMIT` and `MONAD_ZKVM_BUILD_ID`.
