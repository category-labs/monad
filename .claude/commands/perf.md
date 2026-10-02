Measure the performance impact of a VM change.

## Arguments

- `impact [<base>] [<head>]` — compare two commits (default `origin/main` and `HEAD`)
- `history <range>` — measure every VM commit in `<range>` and plot it

## Instructions

`vm-perf` in `scripts/vm/benchmark-analysis` runs `mce` and `vm-micro-benchmarks` under Callgrind and counts the instructions spent compiling each contract in `test/vm/data/compile_benchmarks` and executing each micro benchmark sequence, separately for the compiler and the interpreter. Collection starts and stops per thread on the VM's own entry points, so counts repeat exactly: any change is real. Run it with `uv run --project scripts/vm/benchmark-analysis vm-perf <command>`; see that directory's README.

`impact` and `history` need a spare worktree with initialised submodules; never pass the user's own worktree as `--source`, because the tool checks out, cleans and builds there. Set `CMAKE_CXX_COMPILER_LAUNCHER=ccache` and `CMAKE_C_COMPILER_LAUNCHER=ccache`. The tool builds `mce` and `vm-micro-benchmarks` in `RelWithDebInfo`, fetches the internal evmone and enables the LLVM backend for old commits that need them, and caches a report and the binaries per commit in `-o`.

```bash
uv run --project scripts/vm/benchmark-analysis vm-perf impact origin/main HEAD --timing --source <spare> --build <spare-build> -o <dir>
```

It prints JSON, worst first, and writes `<dir>/impact-<base>-<head>.md`. Each change names the benchmark, its instruction change as a percentage of the whole benchmark run, for micro benchmarks the change in the measured sequence's own cost, and the functions with the largest deltas (`JIT code` is compiled contract code). `--timing` times every changed micro benchmark natively; when time and instructions disagree, trust time, since the change probably traded instructions for fewer stalls. Timing needs an idle machine.

Report what moved (compile time, compiled code, interpreter), by how much and why, reading the named functions before explaining. Changes below 1% in `BASIC_TERN_MATH` and `EXP` with random input are ignored for commits whose benchmarks still use unseeded random calldata.
