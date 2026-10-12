# Manual Monad proving on Vast.ai

This image contains the Monad guest built from source, `ethproofs-client` with
Monad enabled, and the released ZisK **1.3.1-alpha** coordinator, CPU/GPU workers,
emulator and verifier. The CUDA runtime is 12.9.1 on Ubuntu 24.04. It starts idle;
it does not download keys or start proving until requested.

Published image:

```text
ghcr.io/goodlyrottenapple/monad-zisk-prover:1.3.1-alpha-b61e872a
ghcr.io/goodlyrottenapple/monad-zisk-prover@sha256:67d84d07245f17765ab90377d36385e96b3b00dd01d42dcfe4b55ae5b5a4fade
```

## Deploy and copy witnesses

1. Pull the image in a Vast.ai instance using **SSH launch mode**. Use the
   immutable digest reported after publication. For a private GHCR image, give
   Vast a separate classic GitHub token with only `read:packages` and access to
   the package. Nothing needs to be placed in the on-start command.
2. Start with one NVIDIA GPU, ample allocated host RAM, **8 GiB shared memory**
   (`df -h /dev/shm`), and **200 GB disk**. Docker's default 64 MiB shared memory
   causes the ASM emulator to fail during guest setup. The launcher rejects
   less than 1 GiB free; larger witnesses may need more than this minimum.
   GPU/driver/VRAM suitability still needs to be measured on the chosen offer;
   an image build or emulator pass does not establish GPU proving support.
   Keep ports 7000, 50051 and 9090 private. Only SSH access is needed.
3. Copy framed inputs named `<block-number>.bin`, and optionally matching
   `<block-number>.hash` files containing the expected 32-byte Ethereum block
   hash. Use the SSH host and port shown by Vast:

   ```sh
   scp -P PORT 25815003.bin 25815003.hash root@HOST:/workspace/inputs/
   ssh -p PORT root@HOST
   ```

   Obtain the expected hash independently from the corresponding Ethereum
   block header. For the existing block 25815003 fixture it is:

   ```text
   b0fc6aaffcbea12c3226d87d9738ec3d27772c348f607bc92572717da7f63456
   ```

Vast replaces the image entrypoint in SSH mode and starts SSH itself; the image
includes `openssh-server`. No credentials or test witnesses are baked into it.
See [Vast's custom-image documentation](https://docs.vast.ai/documentation/instances/docker-environment).

## Input format and fast execution check

The input is one `ZiskStdin` frame: 8-byte little-endian witness length, raw
Monad RLP witness, then zero padding to 8-byte alignment. Raw `.witness` files
need framing **once**; existing framed `.bin` files should be copied directly.

```sh
witness.py frame 25815003.witness /workspace/inputs/25815003.bin
witness.py check /workspace/inputs/25815003.bin \
  b0fc6aaffcbea12c3226d87d9738ec3d27772c348f607bc92572717da7f63456
```

`check` runs `ziskemu` and compares the complete public block hash. It needs no
GPU or proving key. It confirms guest execution, not proof generation.

## Prove the folder

```sh
prove-folder.sh /workspace/inputs
# CPU fallback, using the separate released CPU worker:
prove-folder.sh --cpu /workspace/inputs
```

The launcher validates the files, downloads the pinned proving key with its
published checksum, starts one coordinator and one worker, waits for worker
registration, and runs `ethproofs-client` in folder mode. The client uploads
and sets up the guest before proving. Key download and first-run constant-tree
setup may take several minutes. Repeated runs reuse `/workspace/keys` and
`/workspace/cache`; keep those directories to retain the setup work.

A run directory under `/workspace/runs/` contains:

- `coordinator.log`, `worker.log`, and `ethproofs-client.log`;
- `proofs.csv` with the client's timing data;
- `proofs/<block>_proof.zisk`, an SDK proof accepted by `cargo-zisk verify`;
- `proofs/<block>_proof.bin`, the client's existing raw proof representation;
- `proofs/<block>_publics.bin`, public-output bytes;
- `versions.json`, recording source pins and the guest hash.

The launcher verifies every SDK proof against the downloaded setup key. If a
matching `.hash` file is supplied, it also compares the guest's execution
output before proving and the proof's saved public output afterwards. A failed
client, missing proof, failed verification, or hash mismatch fails the run.
Ctrl-C stops the client, worker and coordinator. Submission to ethproofs is
not enabled. Folder-mode gas and transaction statistics remain placeholders.

You can repeat the checks manually:

```sh
cargo-zisk verify --proof /workspace/runs/RUN/proofs/25815003_proof.zisk \
  --setup-vk /workspace/keys/provingKey/zisk/vadcop_final/vadcop_final.verkey.json
witness.py publics /workspace/runs/RUN/proofs/25815003_publics.bin \
  b0fc6aaffcbea12c3226d87d9738ec3d27772c348f607bc92572717da7f63456
```

Configuration: `KEY_ROOT` changes the download/cache location;
`PROVING_KEY` selects an already-installed compatible key without downloading;
`WORKER_TIMEOUT` defaults to 1800 seconds; `PROVE_TIMEOUT` defaults to 14400
seconds per proof. An optional second launcher argument selects a **new** run
directory. Inputs and run output must be separate directories. Stop processes
from a previous manual cluster before launching another one.

## Build

From a complete Monad checkout with submodules and the ZisK/RISC-V build
prerequisites installed:

```sh
RISCV_TOOLCHAIN_DIR=/path/to/riscv_gcc \
  docker/zisk/build.sh /path/to/monad /path/to/zisk-ethproofs \
  ghcr.io/goodlyrottenapple/monad-zisk-prover:1.3.1-alpha
```

The Monad source must include the `sam/zisk-build-elf` integration and the
ethproofs checkout must include the Monad dependency and SDK-proof saving.
The guest library builds the release ELF locally. Only temporary build output
is copied into the image; no ELF is tracked in Git. The image enables only the Monad input adapter; normal ethproofs builds retain
all existing clients. The client is compiled inside a Debian Bookworm builder so it can run on the Ubuntu 24.04 runtime,
independently of the host's glibc version.

`cargo vendor --locked` resolves private Git dependencies on the host. Configure
Cargo's Git authentication there if needed (`net.git-fetch-with-cli` with your
SSH URL rewrite). Docker builds offline from the vendored snapshot and never
receives a GitHub token or SSH key. The script retains Cargo/Docker caches but
removes its temporary source context. Allow at least 30 GB of free build space
in addition to existing source/dependency caches. `BUILD_JOBS` controls Cargo
parallelism; native upstream make steps may use additional cores.

Test the image before publishing:

```sh
docker run --rm IMAGE check-image.sh
docker run --rm -v /path/to/inputs:/inputs:ro IMAGE \
  witness.py check /inputs/25815003.bin EXPECTED_BLOCK_HASH
# Full CPU proof, with persistent inputs, keys, cache and results:
docker run --rm --shm-size=8g -v /path/to/workspace:/workspace IMAGE \
  prove-folder.sh --cpu /workspace/inputs
docker push IMAGE
```

GPU proving and cold key installation should be tested on the selected Vast
instance before treating this as an unattended service.
