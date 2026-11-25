Measure the performance impact of a VM change.

## Instructions

`vm-perf` in `scripts/vm/benchmark-analysis` runs `mce` and `vm-micro-benchmarks` under Callgrind and counts the instructions spent compiling each contract in `test/vm/data/compile_benchmarks` and executing each micro benchmark sequence, separately for the compiler and the interpreter. Collection starts and stops per thread on the VM's own entry points, so counts repeat exactly: any change is real. Run it with `uv run --project scripts/vm/benchmark-analysis vm-perf <command>`; see that directory's README.

Build `mce` and `vm-micro-benchmarks` for both sides in `RelWithDebInfo` with `-DMONAD_COMPILER_BENCHMARKS=ON` (see `/build`; build the base in a separate worktree after `git submodule update --init --recursive`), then:

```bash
uv run --project scripts/vm/benchmark-analysis vm-perf measure <base-build> -o base.json --cases cases.json
uv run --project scripts/vm/benchmark-analysis vm-perf measure <head-build> -o head.json --cases cases.json
uv run --project scripts/vm/benchmark-analysis vm-perf compare base.json head.json
```

`compare` prints JSON, worst first. Each change names the benchmark, its instruction change as a percentage of the whole benchmark run, for micro benchmarks the change in the measured sequence's own cost, and the functions with the largest deltas (`JIT code` is compiled contract code).

Report what moved (compile time, compiled code, interpreter), by how much and why, reading the named functions before explaining. Instruction counts miss memory and pipeline effects: a change that trades instructions for fewer stalls reads as slower, so say so when a result contradicts the change's intent. Changes below 1% in `BASIC_TERN_MATH` and `EXP` with random input are ignored, because those benchmarks use unseeded random calldata.
