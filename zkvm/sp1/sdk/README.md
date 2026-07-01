# Vendored SP1 zkEVM SDK

These artifacts are **vendored** (copied in-tree, not a submodule) from the SP1
zkEVM SDK. They supply the zkVM-standards C ABI accelerators (the eth-act
`zkvm_accelerators.h` interface) plus the SP1 guest runtime (`_start`, the
allocator, and `read_input`/`write_output` from `zkvm_io.h`) that the monad
guest links against.

| File | Purpose |
|------|---------|
| `libzkevm.a` | Static archive: `_start`, allocator, `read_input`/`write_output`, `zkvm_halt`, and all `zkvm_*` accelerators (keccak256, sha256, ripemd160, blake2f, modexp, bn254, bls12, secp256k1/r1, kzg). |
| `zkvm.ld` | Linker script (`ENTRY(_start)`, RAM layout, heap/stack/input regions). |
| `include/zkvm_accelerators.h` | The accelerator ABI header (matches `zkvm/core/zkvm_accelerators.h`). |

## Source / provenance

- Repo: <https://github.com/succinctlabs/sp1>
- Branch: `tamir/zkevm` (PR [#2763](https://github.com/succinctlabs/sp1/pull/2763), open as of 2026-06-02)
- Pinned commit: `d291ca10f77d55a38b10accd9db52c21daadb6c5`
- Built for target: `riscv64im-succinct-zkvm-elf`

## Refreshing

The SDK commits a prebuilt `zkevm/sdk/` in the source repo. To bump:

```sh
# Sparse, blob-filtered checkout of just the prebuilt SDK at the new SHA.
git clone --filter=blob:none --no-checkout https://github.com/succinctlabs/sp1.git /tmp/sp1-sdk
cd /tmp/sp1-sdk
git sparse-checkout init --cone && git sparse-checkout set zkevm/sdk
git checkout <new-sha>
# Copy the three artifacts back over this directory and update the SHA above.
cp zkevm/sdk/libzkevm.a            <monad>/zkvm/sp1/sdk/libzkevm.a
cp zkevm/sdk/zkvm.ld               <monad>/zkvm/sp1/sdk/zkvm.ld
cp zkevm/sdk/include/zkvm_accelerators.h <monad>/zkvm/sp1/sdk/include/zkvm_accelerators.h
```

If the SDK source ever stops committing a prebuilt `zkevm/sdk/`, build it with
`make sdk` from the repo's `zkevm/` directory (requires the `+succinct`
toolchain), which runs `zkevm-build-sdk` → `sp1_build::build_program_staticlib`.
