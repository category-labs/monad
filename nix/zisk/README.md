# ZisK toolchains and guest

The root flake provides the patched RISC-V GCC, ZisK Rust toolchain and
reference guest ELF. Run the commands below from the repository root.
The guest build requires an x86_64 Linux builder, including from macOS.

Enable flakes in `~/.config/nix/nix.conf`:

```ini
experimental-features = nix-command flakes
```

Alternatively, pass `--extra-experimental-features "nix-command flakes"`
to each Nix command.

## ZisK guest ELF

Build the reference ELF from a clean checkout with initialized submodules:

```shell
git submodule update --init --recursive
nix build '.?submodules=1#zisk-elf'
ls result/   # monad-zkvm-zisk, monad-zkvm-zisk.build.json
```

The recipe pins the source, submodules and toolchains. `zisk.nix` takes
its linker script and Rust toolchain requirement from the ZisK release
selected by `zkvm/zisk/Cargo.lock`. The source fileset excludes large
test-vector submodules from the guest build.

The ELF embeds `monad-zkvm;commit=<sha>;build=<output-name>`, where
`output-name` is the basename of the Nix output path. The install check
verifies this marker. The adjacent manifest records the source commit,
toolchain and dependency paths, ZisK revision, build ID and ELF hash.
Keep it with published artifacts and benchmark results.

Pinned inputs do not establish reproducibility on their own. Rebuild and
let Nix compare the outputs:

```shell
nix build --rebuild '.?submodules=1#zisk-elf'
```

## Development shell

Use the same toolchains and build flags with local edits:

```shell
nix develop .#zisk
cd zkvm/zisk
cargo build --release --locked --target riscv64ima-zisk-zkvm-elf --target-dir target/elf --bin monad-zkvm-zisk
```

The ELF is `target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk`.
Cargo drives the C++ build through CMake; `cargo-zisk` is not required.
Cargo/CMake retain incremental artifacts. Cargo may download locked
dependencies on the first build.

Use `nix develop`, not `nix shell`: setup hooks configure the Rust wrapper,
linker script and bindgen. The shell clears inherited host compiler flags,
global Rust flags and build stamps. Development ELFs default to
`monad-zkvm;commit=none;build=none`; they do not undergo the reference
identity check. The shell does not supply `ziskemu` or the prover.

`build-env.nix` enables DMA and LTO for both paths. Override
`MONAD_ZKVM_ZISK_DMA` or `MONAD_ZKVM_ZISK_LTO` to compare configurations.
Direct Cargo benchmark builds outside the shell must enable both explicitly.
Additional CMake definitions go in `MONAD_ZKVM_CMAKE_ARGS` as shell-quoted
`-DNAME=VALUE` words. See [guest usage](../../zkvm/README.md#zisk).

## GCC and DMA

```shell
nix build .#riscv64-none-elf-toolchain
./result/bin/riscv64-none-elf-gcc -dumpfullversion
```

The toolchain uses nixpkgs GCC **15.2.0** with the
[ZisKethone DMA patch](https://github.com/0xPolygonHermez/ziskethone/blob/8bede62c7c9e843d1c2163eb05c56794ce706552/cpp-guest/patches/gcc/gcc-15.2.0/0001-riscv-zisk-dma-lowering.patch),
pinned by revision and hash in `riscv64-none-elf-toolchain/default.nix`.
`-mzisk-dma` lowers eligible block memory operations to ZisK DMA markers.
It is off by default in GCC and enabled by the guest recipe.

The toolchain build compiles `probe-dma.c` and checks for the DMA marker
at port `0x813`. This checks lowering for the probe, not ELF identity or
performance. Rebuild the toolchain and guest after changing the patch.

The cross target is `rv64ima/lp64`, so newlib uses the soft-float ABI
required by the guest, unlike nixpkgs's `lp64d` embedded default.
The recipe checks GCC's exact version and its major against
`scripts/ubuntu-build/toolchain.env`; Docker also compares the full host
and cross-compiler versions. Update these checks together when changing
the compiler pin or `flake.lock`.

## Rust toolchain

```shell
nix build .#zisk-rust-toolchain
./result/bin/rustc --version
```

`rust-toolchain/default.nix` pins ZisK Rust **4.1.0** by tag and archive
hash, including the `riscv64ima-zisk-zkvm-elf` target libraries. Nix patches
only host binaries. Evaluation checks that its major matches the pinned
ZisK release's requirement.

The `RUSTC_WRAPPER` normalizes build paths and root-crate metadata to avoid
embedding temporary build-directory names. Its script documents the two
transformations.

## Package layout

The root `flake.nix` exports the toolchains through `nix/overlay.nix` as
`overlays.default`. ZisK packages live in `nix/zisk/`;
`nix/toolchain-env.nix` reads the repository's compiler-version pin.
Docker copies `flake.nix`, `flake.lock`, `nix/` and
`scripts/ubuntu-build/toolchain.env` into a temporary Git flake.

nixpkgs provides dependency packaging and binary substitutes, avoiding
manual toolchain bootstrap scripts. Cold-build time depends on available
substitutes and builder resources.
