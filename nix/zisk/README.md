# zkVM toolchains and guest

Builds the `riscv64-none-elf` GCC used to cross-compile the zkVM guest
(`zkvm/guest`), with the ZisK backend patches applied (see
`riscv64-none-elf-toolchain/README.md`), the Rust toolchain that links the
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
nix build .#riscv64-none-elf-toolchain
cmake -B build-zkvm -S zkvm/guest \
    -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf.cmake \
    -DRISCV_TOOLCHAIN_DIR=$PWD/result \
    -DCMAKE_BUILD_TYPE=Release
```

Both toolchains are ordinary packages added by `overlay.nix`, which the
flake exports as `overlays.default` for other package sets to apply.

The flake lives at the repository root, its overlay in `nix/`, and the ZisK
packages, with their patches and compiler probes, in `nix/zisk/`, so it must
be evaluated from a tree that holds all of them: the repository itself, or a copy of `flake.nix`, `flake.lock`
and `nix/` built as a Git flake
(`git+file://<copy>#riscv64-none-elf-toolchain`), as `docker/Dockerfile`
does.

## ZisK patches

`riscv64-none-elf-toolchain/default.nix` takes GCC 15.2.0 from the pinned nixpkgs
and applies two patches after nixpkgs's own: ZisK's DMA lowering patch,
fetched from
[ziskethone](https://github.com/0xPolygonHermez/ziskethone/tree/develop/cpp-guest/patches/gcc/gcc-15.2.0)
at a pinned commit and hash, then the vendored byte-store patch. They add
two options, both disabled by default:

- `-mzisk-dma` lowers block memory operations to ZisK DMA markers.
- `-mzisk-clean-byte-stores` prefers zero-extended byte constants and additions.

The reference guest build explicitly enables both. After the symlink farm is
assembled, `riscv64-none-elf-toolchain/tests/check-probes.sh` compiles two probes and requires the
assembly each one documents (`csrs 0x813` for a block `memcpy`; `li ...,184`
and `addi ...,...,128` for a byte constant and a byte addition), so an
unpatched or mis-patched compiler fails to build rather than quietly
building a slower guest. To check an externally installed compiler, run:

```sh
bash nix/zisk/riscv64-none-elf-toolchain/tests/check-probes.sh /path/to/riscv64-none-elf-gcc
```

When changing a patch or the pinned ziskethone commit, rebuild the toolchain
and guest. Do not infer ELF identity from a passing probe.

## ZisK Rust toolchain

`zisk-rust-toolchain` is the compiler that builds `ziskos` and the guest's
Rust entry point: 0xPolygonHermez's rustc fork with the
`riscv64ima-zisk-zkvm-elf` target. `cargo-zisk toolchain install` fetches
the same prebuilt archive but takes the newest `zisk-4.x.y` release at
install time, so two machines can hold different compilers without any
record of it. The ZisK source names only the major of the toolchain it
wants, so `rust-toolchain/default.nix` pins the release tag and the archive
hash itself and relinks the binaries for nix. To bump it, change `tag`
and replace the hash with the one the first build reports. Evaluation
fails if the tag's major is not the one the pinned ZisK release asks for,
so a ziskos bump that moves to a new toolchain major, or a toolchain bump
ahead of ziskos, is caught before anything is built.

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
script `cargo-zisk` would supply, which `zisk.nix` takes from the
ZisK release `zkvm/zisk/Cargo.lock` pins `ziskos` to and adds to the
guest's rustflags through its setup hook, and the source commit,
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
cross-compiler settings. `build-env.nix` shares these settings with the
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
the zkVM's no-FPU environment cannot use. `riscv64-none-elf-toolchain/default.nix` declares
`rv64ima` / `lp64` explicitly so newlib is rebuilt for that ABI too. Verify
with:

```shell
./result/bin/riscv64-none-elf-readelf -h <obj> | grep Flags   # 0x0, not 0x4
```

The Nix recipe needs an x86_64 Linux builder, including when run from macOS.
Local development remains available with locally installed tools. The
unordered_dense fork remains pinned by the repository's gitlink and
`.gitmodules`.

Benchmark drivers invoking Cargo directly must pass `MONAD_ZKVM_ZISK_DMA=ON`,
`MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES=ON` and `MONAD_ZKVM_ZISK_LTO=ON`.
`MONAD_ZKVM_OFFICIAL_PROFILE` is no longer used. The commit and build stamps
are supplied separately with `MONAD_ZKVM_GIT_COMMIT` and `MONAD_ZKVM_BUILD_ID`.
