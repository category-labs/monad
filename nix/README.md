# zkVM builds with Nix

Enable flakes in `~/.config/nix/nix.conf`:

```
experimental-features = nix-command flakes
```

Or pass `--extra-experimental-features "nix-command flakes"` to each `nix`
command, as `docker/Dockerfile` does.

## Complete ZisK guest

On **x86_64 Linux**, build the guest ELF and run its audit in one derivation:

```shell
# From the repository root, with a clean, committed worktree.
git submodule update --init --recursive
nix build --option sandbox true --option sandbox-fallback false \
  "git+file://$PWD?dir=nix&submodules=1#zisk"
```

The Git URL includes the submodules at their recorded revisions. Nix refuses
the audited package on a dirty tree, since its ELF embeds the source commit.
Use the existing `zkvm/zisk/build.sh` for development and measurements of
uncommitted changes. macOS needs an x86_64 Linux builder for this package.

The recipe pins nixpkgs, builds GCC 15.2.0 with the three vendored ZisK patches,
and uses hash-pinned ZisK Rust 4.0.0 and `cargo-zisk` 1.3.2-alpha releases.
Cargo dependencies come from `zkvm/zisk/Cargo.lock`, with content hashes for
its two Git sources. Fetching happens in separate Nix dependencies; the guest
build runs offline, with no access to the caller's Cargo or compiler caches.

Outputs:

- `result/bin/monad-zkvm-zisk`: the complete RISC-V guest ELF.
- `result/bin/monad-zkvm-zisk.build.json`: the post-link audit and ELF hash.
- `result/share/monad-zisk/`: the Nix and Cargo locks, CMake profile and input
  store paths used for this build.

**Audited** means that the ELF passed the checks in
`zkvm/zisk/audit-official-build.py`: profile identity, runtime pin, flags and
the code assumptions those checks cover. Nix fixes the declared inputs and
isolates the build; neither claim is a demonstration of bit-for-bit
reproducibility. It also does not establish guest correctness. The audit
records `builder-snapshot` because Nix exports sources without `.git`; the
revision is supplied by the clean Git flake, not reconstructed by the audit.

To test repeatability on one builder, rebuild without substituting the final
output and compare it with the existing result:

```shell
nix build --option sandbox true --option sandbox-fallback false --rebuild \
  "git+file://$PWD?dir=nix&submodules=1#zisk"
```

This checks that rebuild, not reproducibility across all machines. Keep the
existing performance series as its own evidence: switching compilers or
runtime libraries can change the ELF and requires fresh measurements.

## RISC-V cross toolchain

Builds the `riscv64-none-elf` GCC used to cross-compile the zkVM guest
(`zkvm/guest`). CI consumes this from `docker/Dockerfile`; the same output
works locally.

```shell
nix build ./nix#toolchainEnv
RISCV_TOOLCHAIN_DIR=$PWD/result zkvm/zisk/build.sh --archive
```

### Why nix

`riscv-gnu-toolchain` builds by cloning binutils, gdb and newlib from
sourceware.org, which rate limits (HTTP 429) and has made cold builds fail
outright. nixpkgs fetches hash-pinned source tarballs from its own CDN
instead, so a cold build depends only on `cache.nixos.org`.

A cold build takes roughly 8 minutes on 16 cores. Only stage-1 GCC, newlib
and the final GCC are compiled; everything else, cross binutils included, is
substituted from `cache.nixos.org`. That is cheap enough that no additional
binary cache is needed — the docker layer cache absorbs the common case, and
a miss costs minutes rather than the tens of minutes a full
`riscv-gnu-toolchain` bootstrap would.

### Pinning

`flake.lock` pins nixpkgs. The pin is chosen so GCC is **15.2.0**, matching
both the Ubuntu host `gcc-15` and the GCC that `riscv-gnu-toolchain`
2026.05.06 built. Keeping the cross and host compilers in lockstep is
deliberate; check it after bumping:

```shell
nix build ./nix#toolchainEnv
./result/bin/riscv64-none-elf-gcc -dumpfullversion   # must match gcc-15 -dumpfullversion
nix flake update --flake ./nix                       # to bump
```

### Soft float

The stock `pkgsCross.riscv64-embedded` target is `lp64d` (hard float), which
the zkVM's no-FPU environment cannot use. `riscv64-toolchain.nix` declares
`rv64ima` / `lp64` explicitly so newlib is rebuilt for that ABI too. Verify
with:

```shell
./result/bin/riscv64-none-elf-readelf -h <obj> | grep Flags   # 0x0, not 0x4
```
