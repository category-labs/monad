# Monad Execution

## Overview

This repository contains the execution component of a Monad node. It
handles the transaction processing for new blocks, and keeps track of
the state of the blockchain. Consequently, this repository contains
the source code for Category Labs' custom
[EVM implementation](https://docs.monad.xyz/monad-arch/execution/native-compilation),
its [database implementation](https://docs.monad.xyz/monad-arch/execution/monaddb),
and the high-level [transaction scheduling](https://docs.monad.xyz/monad-arch/execution/parallel-execution).
The other main repository is [monad-bft](https://github.com/category-labs/monad-bft),
which contains the source code for the consensus component.

## Building the source code

### Package requirements

Execution has two kinds of dependencies on third-party libraries:

1. **Self-managed**: execution's CMake build system will checkout most of
   its third-party dependencies as git submodules, and build them as part
   of its own build process, as CMake subprojects; this will happen
   automatically during the build, but you must run:

   ```shell
   git submodule update --init --recursive
   ```

   after checking out this repository.

2. **System**: some dependencies are expected to already be part of the
   system in a default location, i.e., they are expected to come from the
   system's package manager. The primary development platform is Ubuntu.
   The scripts `scripts/ubuntu-build/install-tools.sh`,
   `scripts/ubuntu-build/install-deps.sh`, and
   `scripts/ubuntu-build/install-boost.sh` install all required system
   packages. On an Ubuntu host, first run `sudo apt-get update`, then run
   these scripts with elevated privileges (for example, via `sudo`, or as
   root).

### Minimum development tool requirements

- gcc-15 or clang-19
- CMake 3.27
- OpenSSL 3.5
- Even when using clang, the only standard library supported is libstdc++;
  libc++ may work but it is not a tested platform

### CPU compilation requirements

As explained in the [hardware requirements](https://docs.monad.xyz/monad-arch/hardware-requirements),
a Monad node requires a relatively recent CPU. Execution explicitly
requires this to compile: it needs to emit machine code that is only
supported on recent CPU models, for fast cryptographic operations.

The minimum ISA support corresponds to the [x86-64-v3](https://en.wikipedia.org/wiki/X86-64#Microarchitecture_levels)
feature level. Consequently, the minimum flag you must pass to the compiler
is `-march=x86-64-v3`, or alternatively `-march=haswell` ("Haswell" was
the codename of the first Intel CPU to support all of these features).

You may also pass any higher architecture level if you wish, although
the compiled binary may not work on older CPUs. The execution docker
files use `-march=haswell` because it tries to maximize the number of
systems the resulting binary can run on. If you are only running locally
(i.e., the binary does not need to run anywhere else) use `-march=native`.

### Compiling the execution code

First, change your working directory to the root directory of the execution
git repository root and then run:

```shell
CC=gcc-15 CXX=g++-15 CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake \
./scripts/configure.sh && ./scripts/build.sh
```

The above command will do several things:

- Use gcc-15 instead of the system's default compiler

- Emit machine code using Haswell-era CPU extensions, via the toolchain
  file `category/core/toolchains/gcc-avx2.cmake`; the toolchain file sets
  `-march=haswell` for C, C++, and assembly sources.

- Run CMake, and generate a [ninja](https://ninja-build.org/) build
  system in the `<path-to-execution-repo>/build` directory with
  the [`CMAKE_BUILD_TYPE`](https://cmake.org/cmake/help/latest/variable/CMAKE_BUILD_TYPE.html)
  set to `RelWithDebInfo` by default

- Build the CMake `all` target, which builds everything

The compiler is selected via the `CC`/`CXX` environment variables, which
CMake reads at configuration time.  The CPU target is set via the toolchain
file, passed through the `CMAKE_TOOLCHAIN_FILE` environment variable.  If
you want debug binaries instead, you can also pass `CMAKE_BUILD_TYPE=Debug`
via the environment.

When finished, this will build all of the execution binaries. The main one is
the execution daemon, `build/cmd/monad`. This binary can provide block
execution services for different EVM-compatible blockchains:

- When used as part of a Monad blockchain node, it behaves as the block
  execution service for the Category Labs consensus daemon (for details, see
  [here](docs/overview.md#how-is-execution-used)); when running in this mode,
  Monad EVM extensions (e.g., Monad-style staking) are enabled

- It can also replay the history of other EVM-compatible blockchains, by
  executing their historical blocks as inputs; a common developer workflow
  (and a good full system test) is to replay the history of the original
  Ethereum mainnet and verify that the computed Merkle roots match after
  each block

You can also run the full test suite in parallel with:

```
CTEST_PARALLEL_LEVEL=$(nproc) ctest
```

### Private domain HPKE keys

Private domain payload execution is encrypted-only. Configure each domain
together with its domain-local DomainSpoke address and RFC 9180 receiver key,
and point the scanner at the L1 DomainHub (see
[README_DOMAINS.md](README_DOMAINS.md)):

```shell
monad ... \
  --private-domain 85679 0x5FbDB2315678afecb367f032d93F642f64180aa3 /secure/domain-85679-private.pem \
  --private-domain-sequencer 0x5FbDB2315678afecb367f032d93F642f64180aa3
```

Generate the unencrypted P-256 PKCS#8 PEM private key and matching public key
with OpenSSL:

```shell
openssl genpkey -algorithm EC \
  -pkeyopt ec_paramgen_curve:P-256 \
  -out domain-private.pem \
  -outpubkey domain-public.pem
chmod 600 domain-private.pem
```

Encrypted private-key PEM files are not supported. Back up the private key and
retain it for historical replay. Distribute the public key to transaction
producers over an authenticated external channel. Every replica executing the
same domain must share this receiver private key; the profile does not
support distinct per-replica keys.

The fixed profile is RFC 9180 Base mode with DHKEM(P-256, HKDF-SHA256),
HKDF-SHA256, AES-128-GCM, empty AAD, and info
`private-domain-hpke-rfc9180-v1`. The outer bytes payload is the 65-byte
uncompressed encapsulated P-256 point followed by ciphertext and tag. The
encrypted plaintext is `0x01 || signed_transaction_bytes`.

Base mode does not authenticate the sender and does not provide forward
secrecy after receiver-key compromise. Empty AAD permits a valid ciphertext to
be moved to another matching outer envelope; inner transaction nonce and chain
validation remain the replay boundary. Decrypted domain transactions are
persisted in the local database. Reverted outer calls are still scanned, so
the DomainHub call is not a producer-authentication boundary and operators
must account for unauthenticated gasless work in their denial-of-service model.

## Compiling zkVM binary

To compile monad as a guest program for various zkVMs, such as ZisK or SP1, we need to use a riscv64 cross-compiler. The easiest way to do this is to use the [riscv-gnu-toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain) which includes newlib. The cmake build extracts only the needed libc objects (setjmp/longjmp) from the unmodified newlib; malloc and syscalls are weakly linked by the zkVM frameworks.

```shell
cmake -B build-zkvm -S zkvm/guest \
   -DCMAKE_TOOLCHAIN_FILE=$PWD/category/core/toolchains/riscv64-elf.cmake \
   -DRISCV_TOOLCHAIN_DIR="path/to/riscv_gcc" \
   -DCMAKE_BUILD_TYPE=Release -GNinja
```

We can then build the static library:

```shell
cmake --build build-zkvm --target monad-zkvm --parallel
```

## A tour of execution

To understand how the source code is organized, you should start by reading
the execution [developer overview](docs/overview.md), which explains how
execution and consensus fit together, and where in the source tree you can
find different pieces of functionality.
