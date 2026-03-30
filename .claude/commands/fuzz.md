Run VM fuzzers for the monad C++ project.

## Arguments

The user may pass arguments like:
- `compiler` — run the compiler fuzzer (default)
- `typechecker` — run the typechecker fuzzer
- `staking` — run the staking contract fuzzer
- `--seed <N>` — set the random seed
- `--multi` — run multiple fuzzer sessions via tmux
- `status` — check tmux fuzzer session status
- `kill` — stop all tmux fuzzer sessions

## Instructions

You are running fuzzers for the monad C++ project located at $CWD.

### Build requirements

The compiler and typechecker fuzzers require `MONAD_COMPILER_TESTING=ON` at configure time and `third_party/evmone` (see `/build` for evmone setup instructions). The staking contract fuzzer is always built with no special options.

If the fuzzer binaries don't exist, offer to reconfigure. The CI fuzzing configuration is:
```bash
CC=clang-19 CXX=clang++-19 cmake -G Ninja -B build \
  -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE=Release \
  -DMONAD_COMPILER_TESTING=ON
```
Then build the fuzzer target:
```bash
cmake --build build --target monad-compiler-fuzzer --parallel
```

### Fuzzer binaries

| Binary | Target | Description |
|--------|--------|-------------|
| `build/test/vm/fuzzer/monad-compiler-fuzzer` | `monad-compiler-fuzzer` | Fuzzes the JIT compiler |
| `build/test/vm/fuzzer/monad-typechecker-fuzzer` | `monad-typechecker-fuzzer` | Fuzzes the typechecker |
| `build/category/execution/monad_staking_contract_fuzzer` | `monad_staking_contract_fuzzer` | Fuzzes the staking contract |

### Single-process run

Use the wrapper scripts which set `MONAD_COMPILER_FUZZING=1`:
```bash
# Compiler fuzzer (pass --implementation compiler or --implementation interpreter, and --seed N)
scripts/vm/fuzzer.sh --implementation compiler --seed 143
# Typechecker fuzzer
scripts/vm/typechecker-fuzzer.sh --seed 143
# Staking contract fuzzer (run directly)
build/category/execution/monad_staking_contract_fuzzer
```

### Multi-process run via tmux

`scripts/vm/tmux-fuzzer.sh` manages multiple fuzzer sessions (11 compiler + 2 interpreter by default):
```bash
scripts/vm/tmux-fuzzer.sh start --base-seed=143   # start all sessions
scripts/vm/tmux-fuzzer.sh status                   # check which are running
scripts/vm/tmux-fuzzer.sh kill                     # stop all sessions
```
Logs go to `tmux-fuzzer-log/`.

### Important

- Always run commands from the project root directory: $CWD
- Do NOT modify any source files
