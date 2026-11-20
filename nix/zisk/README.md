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
nix build --option sandbox true --option sandbox-fallback false '.?submodules=1#zisk-elf'
ls result/   # monad-zkvm-zisk, monad-zkvm-zisk.build.json
```

The recipe pins the source, submodules and toolchains. `zisk.nix` pins
the ZisK release, by revision and hash, that supplies the linker script and
the Rust toolchain requirement; evaluation fails unless
`zkvm/zisk/Cargo.lock` names the same release. The source fileset excludes
large test-vector submodules from the guest build.

The ELF embeds `monad-zkvm;commit=<sha>;build=<output-name>`, where
`output-name` is the basename of the Nix output path. The install check
verifies this marker. The adjacent manifest records the source commit,
toolchain and dependency paths, ZisK revision, build ID and ELF hash.
Keep it with published artifacts and benchmark results.

The build directory reaches the ELF through panic locations and Cargo's
crate metadata. The Nix sandbox fixes it at `/build`, so the recipe fails
outside the sandbox. The two options above make Nix report a missing
sandbox itself instead of falling back to an unsandboxed build.

Pinned inputs do not establish reproducibility on their own. Rebuild and
let Nix compare the outputs:

```shell
nix build --rebuild --option sandbox true --option sandbox-fallback false '.?submodules=1#zisk-elf'
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

Use `nix develop`, not `nix shell`: setup hooks configure the linker
script and bindgen. The shell clears inherited host compiler flags,
global Rust flags and build stamps. Development ELFs default to
`monad-zkvm;commit=none;build=none`; they do not undergo the reference
identity check, and they embed the checkout's path. The shell does not
supply `ziskemu` or the prover.

`build-env.nix` enables DMA and LTO for both paths. Override
`MONAD_ZKVM_ZISK_DMA` or `MONAD_ZKVM_ZISK_LTO` to compare configurations.
Direct Cargo benchmark builds outside the shell must enable both explicitly.
See [guest usage](../../zkvm/README.md#zisk).

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

`rust-toolchain.nix` pins ZisK Rust **4.1.0** by tag and archive
hash, including the `riscv64ima-zisk-zkvm-elf` target libraries. Nix patches
only host binaries. Evaluation checks that its major matches the pinned
ZisK release's requirement.

## Package layout

The root `flake.nix` exports the toolchains through `nix/overlay.nix` as
`overlays.default`. ZisK packages live in `nix/zisk/`;
`nix/toolchain-env.nix` reads the repository's compiler-version pin.
Docker copies `flake.nix`, `flake.lock`, `nix/` and
`scripts/ubuntu-build/toolchain.env` into a temporary Git flake.

nixpkgs provides dependency packaging and binary substitutes, avoiding
manual toolchain bootstrap scripts. Cold-build time depends on available
substitutes and builder resources.

## Regenerating the interpreter frame policy

After changing a handler or the RISC-V compiler, run this from the repository
root in the ZisK development shell, with the submodules initialized. Use the
same CMake settings as the guest you want to check. For the reference recipe:

```sh
export MONAD_ZKVM_CMAKE_ARGS="-DMONAD_ZKVM_NO_MERGE_CONSTRAINTS=ON -DCMAKE_EXPORT_COMPILE_COMMANDS=ON -DMONAD_ZKVM_NO_DIRTY_ACCOUNTS=ON -DMONAD_ZKVM_VARCODE_CACHE=ON -DMONAD_ZKVM_WIDE_MEMORY_SIZE=ON -DMONAD_ZKVM_KECCAKF_MEMO=ON"
python3 nix/regenerate-frame-opcodes.py \
    --binutils-prefix "$RISCV_TOOLCHAIN_DIR/bin/riscv64-none-elf-"
```

The tool runs Cargo on a temporary source copy with an empty `keeps_frame`
list. The reference ELF audit reads the local symbols emitted at the manual
`jalr` instructions in the prefix and lag dispatch macros. It follows each
handler from entry and verifies the native frame and callee-saved registers
at the marked addresses, including zero-offset jumps. Both marker families
must be present, and every listed site must be reached and checked. The
build manifest records their count as `interpreter_manual_jumps`.
An unsafe jump in any revision or lag copy excludes that opcode. Production
and the deferred-gas self-test share a policy; the eager-gas self-test has its
own. The tool rebuilds and audits all three until they pass. Only then does
it replace `category/vm/interpreter/frame_opcodes.inc`. Use `--check` to
compare without writing. A link failure (including a slot overflow), a jump
in a separate helper or PUSH pair, or an unsafe jump in an already excluded
handler stops generation for inspection. Probe ELFs are never executed.
Ordinary builds use the checked-in list.
