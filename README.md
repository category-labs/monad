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
   system's package manager. The primary development platform is Ubuntu, so
   the required packages use the Debian/Ubuntu package names; an up-to-date
   list of the required system dependencies can be found in the docker
   configuration file `docker/release.Dockerfile` (you will need all
   the packages installed via the `apt install` commands)

### Minimum development tool requirements

- gcc-15 or clang-19
- CMake 3.27
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
CC=gcc-15 CXX=g++-15 CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" \
./scripts/configure.sh && ./scripts/build.sh
```

The above command will do several things:

- Use gcc-15 instead of the system's default compiler

- Emit machine code using Haswell-era CPU extensions

- Run CMake, and generate a [ninja](https://ninja-build.org/) build
  system in the `<path-to-execution-repo>/build` directory with
  the [`CMAKE_BUILD_TYPE`](https://cmake.org/cmake/help/latest/variable/CMAKE_BUILD_TYPE.html)
  set to `RelWithDebInfo` by default

- Build the CMake `all` target, which builds everything

The compiler and CPU options are injected via environment variables that
are read by CMake.  If you want debug binaries instead, you can also pass
`CMAKE_BUILD_TYPE=Debug` via the environment.

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

## A tour of execution

To understand how the source code is organized, you should start by reading
the execution [developer overview](docs/overview.md), which explains how
execution and consensus fit together, and where in the source tree you can
find different pieces of functionality.
