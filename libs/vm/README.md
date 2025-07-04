# Monad EVM Compiler

> [!WARNING]  
> This project is an untested work in progress.

An implementation of an [EVMC][evmc]-compatible implementation of the Ethereum
Virtual Machine, using LLVM to compile EVM bytecode to native code for faster
execution. The work in this project is a C++ reimplementation of the
[`monad-jit`][jit] project, with the eventual aim of merging the compiler into
the core Monad monorepo.

## Building & Running

The compiler is built and tested in CI on Ubuntu 24.04. To build locally, first
install the following dependencies via `apt`:
```
build-essential
cmake
llvm-19-dev
libbenchmark-dev
libcli11-dev
libgmock-dev
libgtest-dev
libtbb-dev
```

Then, from the project root:
```console
$ git submodule update --init --recursive
$ cmake -S . -B build
$ cmake --build build
```

## Testing

### Ethereum Tests

The ethereum blockchain tests can be executed with the command
```
$ build/test/blockchain/compiler-blockchain-tests
```
It will implicitly skip blockchain tests which
* contain invalid blocks and
* contain unexpected json format and
* execute slowly.

Use the `--gtest_filter` flag to enable or disable specific tests. See
```
$ build/test/blockchain/compiler-blockchain-tests --help
```

### Configuring blockchain test VM

Environment variables can be used for debugging tests based on the
blockchain test vm. Both the fuzzer and the etherum tests are based on
the blockchain test vm.

By setting the `MONAD_COMPILER_ASM_DIR` environment
variable to a valid directory, the compiler will print contract
assembly code in files to this directory.

The `MONAD_COMPILER_DEBUG_TRACE=1` environment variable can be
used to enable a runtime debug trace. The generated assembly code
will contain calls to a runtime function, which prints gas
remaining when a jump destination is reached. For example,
```
$ export MONAD_COMPILER_ASM_DIR=/tmp/debug
$ export MONAD_COMPILER_DEBUG_TRACE=1
$ build/test/blockchain/compiler-blockchain-tests \
    --gtest_filter="*.jumpiNonConst"
```
will print something like
```
...
Block 0x00: gas remaining: 379000
Block 0x2d: gas remaining: 378784
Block 0x00: gas remaining: 379000
...
```
and create assembly file with name the address of the called contract,
```
/tmp/debug/095e7baea6a6c7c4c2dfeb977efac326af552d87
```

To run the blockchain test vm using only evmone without compiler,
define the `MONAD_COMPILER_EVMONE_ONLY=1` environment variable:
```
$ export MONAD_COMPILER_EVMONE_ONLY=1
$ build/test/blockchain/compiler-blockchain-tests
```

### The `MONAD_COMPILER_TESTING` configuration

If the project is configured with `MONAD_COMPILER_TESTING` enabled, e.g.
```
$ cmake -S . -B build -DMONAD_COMPILER_TESTING=ON
```
then debug assertions will be enabled even when the `NDEBUG` macro is
defined. With `MONAD_COMPILER_TESTING` configuration one can also define
the `EVMONE_DEBUG_TRACE=1` environment variable to get runtime debug
information from evmone and the test host, defined in the evmone project.
For example
```
$ export MONAD_COMPILER_DEBUG_TRACE=1
$ export EVMONE_DEBUG_TRACE=1
$ build/test/blockchain/compiler-blockchain-tests \
    --gtest_filter="*.jumpiNonConst"
...
offset: 0x59  opcode: 0x90  gas_left: 29977858
offset: 0x5a  opcode: 0x62  gas_left: 29977855
offset: 0x5e  opcode: 0x1  gas_left: 29977852
offset: 0x5f  opcode: 0x55  gas_left: 29977849
offset: 0x60  opcode: 0x0  gas_left: 29975649
START baseline_execute address 095E7BAEA6A6C7C4C2DFEB977EFAC326AF552D87 with gas = 379000
Block 0x00: gas remaining: 379000
Block 0x2d: gas remaining: 378784
END baseline_execute address 095E7BAEA6A6C7C4C2DFEB977EFAC326AF552D87
offset: 0x00  opcode: 0x33  gas_left: 30000000
offset: 0x01  opcode: 0x73  gas_left: 29999998
...
offset: 0x16  opcode: 0x14  gas_left: 29999995
offset: 0x5f  opcode: 0x55  gas_left: 29977849
offset: 0x60  opcode: 0x0  gas_left: 29975649
START baseline_execute address 095E7BAEA6A6C7C4C2DFEB977EFAC326AF552D87 with gas = 379000
Block 0x00: gas remaining: 379000
END baseline_execute address 095E7BAEA6A6C7C4C2DFEB977EFAC326AF552D87
```

Note that evmone is being used for executing certain contracts, even when
the `MONAD_COMPILER_EVMONE_ONLY=1` environment variable is not set.
For example, `CREATE` and `CREATE2` calls are always executed with evmone.

The lines starting with `offset` contain runtime debug information from
evmone, with one line for each instruction executed by evmone. The
`START` and `END` lines contain information about which contracts are
executing. Lines starting with `Block` contain runtime debug output
from `monad-compiler`.

### Fuzzer

Configure build with testing enabled

```
$ cmake -S . -B build -DMONAD_COMPILER_TESTING=ON
```

and build

```
cmake --build
```

Use the helper script `scrips/fuzzer.sh` to run the fuzzer.

Execute
```
scripts/fuzzer.sh --help
```
for more information.

The script `scripts/tmux-fuzzer.sh` can be used to start concurrent fuzzer
instances in Tmux sessions. Use
```
scripts/tmux-fuzzer.sh start
```
to start the concurrent fuzzer Tmux sessions. Then command
```
scripts/tmux-fuzzer.sh status
```
can be used to query status of the Tmux sessions. Use
```
scripts/tmux-fuzzer.sh kill
```
to kill all the fuzzer Tmux sessions.

### Directory Type Check Test

After building the compiler source code, the `directory-type-check` executable
can be used on a directory containing bytecode contracts. It will recursively
traverse the directory and run the type inference algorithm on all the
contracts. It will additionally run the type checking algorithm to verify the
correctness of the inferred types. For example
```console
build/src/test/utils/directory-type-check my/contracts-dir
```
will print type inference errors to standard error and print contract type
information to standard out. If it prints to standard error, there is bug
somewhere.

## Benchmarks

The project contains several sets of performance benchmarks that are not built
by default. To enable them, set `MONAD_COMPILER_BENCHMARKS=ON` via CMake. This
option is orthogonal to `MONAD_COMPILER_TESTING`; it's possible to build the
benchmark executables with debug assertions enabled, but the results obtained
will not be accurate.

Benchmark executables are:
- `execution-benchmarks`: Run a combination of opcode-specific microbenchmarks
  and summarised transactions from Ethereum history as a benchmark of "real world"
  performance.
- `burntpix-benchmark`: Run the [BurntPix](https://burntpix.com/) generative art
  program with a large cycle count as a "pure computation" benchmark.
- `compile-benchmarks`: Establish how long the native X86 compiler takes to
  compile a set of real and synthetic contracts.

These executables are all implemented using [Google
Benchmark](https://github.com/google/benchmark), and can be controlled
accordingly with command-line arguments.

### Reference Build

As an example, to set up and run the BurntPix benchmarks using GCC 14:
```console
$ CC=gcc-14 CXX=g++-14 cmake                                \
    -S . -B build                                           \
    -G Ninja                                                \
    -DCMAKE_TOOLCHAIN_FILE=cmake/toolchains/gcc-avx2.cmake  \
    -DCMAKE_BUILD_TYPE=Release                              \
    -DMONAD_COMPILER_TESTING=Off                            \
    -DMONAD_COMPILER_BENCHMARKS=On
$ cmake --build build
$ build/test/burntpix_benchmark/burntpix-benchmark
----------------------------------------------------------------------------------
Benchmark                                        Time             CPU   Iterations
----------------------------------------------------------------------------------
burntpix/0x0/0x7a120/interpreter        1025652212 ns   1025644766 ns            1
burntpix/0x0/0x7a120/compiler            509836576 ns    509846789 ns            1
burntpix/0x0/0x7a120/evmone              802911097 ns    802921406 ns            1
...
```

Note the most important points for achieving accurate results (release build,
testing mode disabled, AVX2 toolchain file selected).

### Analysis Scripts

See [here](scripts/benchmark_analysis/README.md) for documentation on a set of
Python scripts that can be used to analyse the results obtained from these
benchmarks.

### Interpreter Opcode Statistics

The interpreter can be configured to print out statistics for each opcode when
the enclosing binary exits. For example, to run a single execution benchmark
ten times and print statistics:
```console
$ CC=gcc-14 CXX=g++-14 cmake                                \
    -S . -B build                                           \
    -G Ninja                                                \
    -DCMAKE_TOOLCHAIN_FILE=cmake/toolchains/gcc-avx2.cmake  \
    -DCMAKE_BUILD_TYPE=Release                              \
    -DMONAD_COMPILER_TESTING=Off                            \
    -DMONAD_COMPILER_BENCHMARKS=On                          \
    -DMONAD_VM_INTERPRETER_STATS=On
$ ./build/test/execution_benchmarks/execution-benchmarks  \
    --benchmark_filter='counting_loop/interpreter'        \
    --benchmark_min_time=10x
...
----------------------------------------------------------------------------
Benchmark                                  Time             CPU   Iterations
----------------------------------------------------------------------------
execute/counting_loop/interpreter   27404557 ns     27404412 ns           10
opcode,name,count,time
1,ADD,655360,14010307
20,EQ,655360,14007292
21,ISZERO,655360,13738208
81,MLOAD,655360,14031804
82,MSTORE,10,3200
87,JUMPI,655360,14742046
91,JUMPDEST,655360,13287609
95,PUSH0,655380,13577208
96,PUSH1,1310720,27168176
127,PUSH32,10,2140
128,DUP1,655360,13579918
```

The code implementing this feature relies on global state and is not
thread-safe; it should only be enabled in limited benchmarking contexts and
never in production.

## Structure

There are four main components:
- A compiler from EVM bytecode to LLVM IR; the programs generated by this
  compiler rely on being linked against a runtime support library, and on being
  run in the context of an EVMC-compatible host.
- A runtime support library for EVM programs that handles interaction with the
  host context (gas calculations etc.).
- An EVMC-compatible VM layer that handles compiling bytecode to LLVM, then
  executing the compiled code via LLVM's JIT implementation.
- A debugging tool that compiles a contract to LLVM IR and dumps the result to
  `stdout`.

## Documentation

To build the project's documentation using [Doxygen][doxygen], run:
```console
$ doxygen
```
from the project root.

On Peach machines, the built documentation needs to be accessed over SSH. To run
a local HTTP server that can be tunneled to your local machine, run:
```console
$ ./scripts/serve-docs.sh
```

Then, on your local machine open an HTTP tunnel over SSH with:
```console
$ ssh -N -L 8000:localhost:8000 <user@some-peach>
```

The documentation is then accessible from `http://localhost:8000` locally.

[doxygen]: https://www.doxygen.nl/
[evmc]: https://github.com/ethereum/evmc
[jit]: https://github.com/monad-crypto/monad-jit
[hunter]: https://github.com/ethereum/evmc/pull/169

## Coverage
To enable coverage statistics set `-DCOVERAGE=ON` when configuring, e.g.
```console
$ cmake -DCMAKE_BUILD_TYPE=Debug -DCOVERAGE=ON -S . -B build -G Ninja
```
After running the desired executable, use `gcovr .` to gather coverage statistics.

## Linting & Formatting

To run the linter:
```console
scripts/check-clang-tidy.sh
```

Automatic fixes can be applied to a clean working tree with:
```console
scripts/apply-clang-tidy-fixes.sh build run-clang-tidy-19
```

To run the formatter, call:
```console
find {cmd,libs,test} -iname '*.h*' -o -iname '*.c*' | xargs clang-format-19 -i
```
Care should be taken to make sure that automatically-fixed code compiles and is
correct.

## Dumping assembly

Passing `-DMONAD_COMPILER_DUMP_ASM=On` to CMake, will dump all `.s` assembly files for the monad code into `build/asm`. One can then use the following vscode extension: https://github.com/dseight/vscode-disasexpl to view the assembly. In order for this to work, add the following setting to `.vscode/settings.json` file inside the `monad-compiler` repo (if your CMake build folder is called something else, modify appropriately):

```json
"disasexpl.associations": {
    "**/*.c": "${workspaceFolder}/build/asm/${fileBasename}.s",
    "**/*.cpp": "${workspaceFolder}/build/asm/${fileBasename}.s"
}
```
