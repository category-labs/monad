# RocksDB migration — `replay_ethereum` perf ledger

One row per PR. The point is **attribution**: if the final RocksDB version is slower
than the MonadDB baseline — or any intermediate PR regresses — the responsible PR is
obvious from the per-PR Δ column.

## Fixed harness (keep identical across runs)

- **Box:** the remote dev server (same machine + device class every run).
- **Invocation:** `replay_ethereum.sh` — `compile.sh` → **prep** → **run**, pinned with
  `cgexec -g memory:replay` + `taskset`.
  - MonadDB track: prep `monad-mpt --storage /dev/triedb --restore <N>.archive`; run
    `cmd/monad --block_db <eth> --nblocks <NB> --nthreads <T> --nfibers <F> --db /dev/triedb
    --chain=ethereum_mainnet --no-compaction`.
  - RocksDB track (from F9): prep = one-time F8 snapshot→RocksDB load producing the seed dir;
    run = same command with `--db <rocksdb_dir> --state-backend=rocksdb` (no `--no-compaction`).
- **Range:** start block `N = 22,830,000` (see `replay_ethereum.sh`); `nblocks`, `nthreads`,
  `nfibers` pinned per run — record them in the row's notes.
- **Method:** capture cold-cache and warm-cache; ≥3 repetitions; record **median + p99**.
- **Metrics:** blocks/s, gas/s, total wall time, per-block exec-vs-commit (`cmt=` field +
  the 500 ms slow-commit warnings in `runloop_ethereum.cpp`), read-stall counts; from F9 also
  RocksDB compaction / write-amp / block-cache hit-rate + the Phase-A miss-batch counters.

## Baseline

Capture the MonadDB numbers **before F1** as the reference, and re-capture whenever the box,
dataset, or block range changes (note it in the row).

| Item | Value |
|------|-------|
| Baseline commit | _TBD — capture pre-F1 MonadDB run_ |
| MonadDB median (blocks/s, gas/s) | _TBD_ |
| MonadDB commit p99 (`cmt=`) | _TBD_ |

## Per-PR runs

Two tracks where applicable. The **MonadDB track must stay flat** while we coexist — a drift
means a PR accidentally regressed the *default* backend. F1–F8 produce no RocksDB replay number
(F8 only builds the seed offline); from **F9** the RocksDB track runs end-to-end every PR.

| PR | Commit | Touches main code? | MonadDB median / p99 | RocksDB median / p99 | Δ vs prev | Δ vs baseline | Notes |
|----|--------|--------------------|----------------------|----------------------|-----------|---------------|-------|
| F1 | `e210f5f4` | no | — | — | — | — | build scaffolding only; no replay run |
| F2 | `9e41ae0d` | no | — | — | — | — | leaf lib (KvStore), zero callers; no replay run |
| F3 | `516d7628` | no | — | — | — | — | test-only parity harness; no replay run |
| F4 | _this commit_ | **yes** (`cmd/monad`, factory) | _pending replay_ | — | _pending_ | _pending_ | `make_db` factory + `--state-backend`; TrieDb stays sole impl, behavior unchanged → MonadDB track must stay flat |

> Regression budget (fill in with the team's tolerance): throughput drop > **X%** or commit-p99
> increase > **Y%** vs the previous PR blocks merge until explained. Planned dips (e.g. F9's
> synchronous WAL, recovered by F10/F11/F12) are annotated with their expected recovery PR.
