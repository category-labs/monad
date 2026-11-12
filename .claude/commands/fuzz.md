Run VM fuzzers for the monad C++ project.

## Arguments

The user may pass arguments like:
- `compiler` — run the compiler fuzzer (default)
- `staking` — run the staking contract fuzzer
- `--seed <N>` — set the random seed
- `--multi` — run parallel fuzzer sessions with `scripts/vm/fuzz.sh`
- `status` — check tmux fuzzer session status
- `kill` — stop all tmux fuzzer sessions

## Instructions

You are running fuzzers for the monad C++ project located at $CWD.

### Build requirements

The compiler fuzzer requires `MONAD_COMPILER_TESTING=ON` at configure time and initialized submodules (`git submodule update --init --recursive`). The staking contract fuzzer is always built with no special options.

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
| `build/category/execution/monad_staking_contract_fuzzer` | `monad_staking_contract_fuzzer` | Fuzzes the staking contract |

### Single-process run

Use the wrapper scripts which set `MONAD_COMPILER_FUZZING=1`:
```bash
# Compiler fuzzer (pass --implementation compiler or --implementation interpreter, and --seed N)
scripts/vm/fuzzer.sh --implementation compiler --seed 143
# Staking contract fuzzer (run directly)
build/category/execution/monad_staking_contract_fuzzer
```

### Multi-process run

`scripts/vm/fuzz.sh` runs parallel fuzzer sessions (11 compiler + 2 interpreter by default, consecutive seeds) and stops at the first failure, printing the failing seed's log:
```bash
scripts/vm/fuzz.sh -s 143              # run until a session fails
scripts/vm/fuzz.sh -c 26 -i 5 -t 420   # what CI runs: 31 sessions for 7 minutes
tmux new -d -s fuzz scripts/vm/fuzz.sh # run in the background
```
Logs go to `fuzzer-log/`.

`scripts/vm/tmux-fuzzer.sh` manages long-running sessions by hand (11 compiler + 2 interpreter by default):
```bash
scripts/vm/tmux-fuzzer.sh start --base-seed=143   # start all sessions
scripts/vm/tmux-fuzzer.sh status                   # check which are running
scripts/vm/tmux-fuzzer.sh kill                     # stop all sessions
```
Logs go to `tmux-fuzzer-log/`.

### Important

- Always run commands from the project root directory: $CWD
- Do NOT modify any source files
