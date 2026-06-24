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
| Baseline commit | _TBD — capture pre-F1 MonadDB run at nb=10000 from block 22,830,000_ |
| MonadDB median (blocks/s, gas/s) | _TBD_ |
| MonadDB commit p99 (`cmt=`) | _TBD_ |

> Informal same-blocks reference (not the formal baseline): a `cache-warmset-coverage`
> MonadDB run over the identical blocks 22,830,001–22,840,000 gave cmt mean 12292µs,
> median 11994µs, p99 22802µs. Useful as a sanity check until a pre-F1 `main` run lands.

## Per-PR runs

Two tracks where applicable. The **MonadDB track must stay flat** while we coexist — a drift
means a PR accidentally regressed the *default* backend. F1–F8 produce no RocksDB replay number
(F8 only builds the seed offline); from **F9** the RocksDB track runs end-to-end every PR.

| PR | Commit | Touches main code? | MonadDB median / p99 | RocksDB median / p99 | Δ vs prev | Δ vs baseline | Notes |
|----|--------|--------------------|----------------------|----------------------|-----------|---------------|-------|
| F1 | `e210f5f4` | no | — | — | — | — | build scaffolding only; no replay run |
| F2 | `9e41ae0d` | no | — | — | — | — | leaf lib (KvStore), zero callers; no replay run |
| F3 | `516d7628` | no | — | — | — | — | test-only parity harness; no replay run |
| F4 | `b5b110ed3` | **yes** (`cmd/monad`, factory) | 353s · tps 5794 · gps 514M · cmt med 12.5ms / p99 24.0ms | — | first MonadDB number | _baseline TBD_ | nb=10000 from block 22,830,000, 3 reps, **0 slow-commits**; behavior-preserving refactor (see run detail) |
| F5 | `423b1f4a4` | **yes** (`trie_db` hot path, guarded) | 354s · tps 5777 · gps 513M · cmt med 12.5ms / p99 24.2ms | — | flat vs F4 (Δ<1%) | _baseline TBD_ | nb=10000, 3 reps, **0 slow-commits**, **no flag** (mirror dormant); within noise of F4 — no regression. Shadow path (`--validate-flat-state`) not yet exercised |

> Regression budget (fill in with the team's tolerance): throughput drop > **X%** or commit-p99
> increase > **Y%** vs the previous PR blocks merge until explained. Planned dips (e.g. F9's
> synchronous WAL, recovered by F10/F11/F12) are annotated with their expected recovery PR.

## Run details

### F4 — commit `b5b110ed3`, `--state-backend=triedb` (MonadDB track)

Config: prep `monad-mpt --restore 22830000.archive`; run `--nblocks 10000 --db /dev/triedb
--no-compaction`, 3 reps, cgexec/taskset pinned. `--state-backend` defaults to triedb, so this
exercises the new `make_db` path on the unchanged MonadDB engine. Source logs (since overwritten
by later runs): `/tmp/log_062226_rocksdb_22830000_10000_{1,2,3}`.

| rep | wall | tps | gps | cmt median | cmt p99 | cmt max | slow >500ms |
|-----|------|-----|-----|-----------|---------|---------|-------------|
| 1 | 363s | 5634 | 500M | 12490µs | 24007µs | 104019µs | 0 |
| 2 | 341s | 5997 | 532M | 12498µs | 23703µs | 69821µs | 0 |
| 3 | 353s | 5794 | 514M | 12496µs | 24284µs | 132486µs | 0 |
| **median** | **353s** | **5794** | **514M** | **12496µs** | **24007µs** | — | **0** |

Reps are tight (cmt median within 8µs; tps within ~6%). Versus the same-blocks
`cache-warmset-coverage` MonadDB reference (cmt median 11994µs / p99 22802µs), F4 is within ~4–5%
— run-to-run noise, and that branch is not the formal baseline. **No regression evident.** F4 only
relocates the identical `mpt::Db` + `TrieDb` construction into `make_db`, so the hot
execute/commit path is unchanged. A formal Δ-vs-baseline still needs a pre-F1 `main` run at this
exact config (nb=10000 from 22,830,000).

### F5 — commit `423b1f4a4`, no flag (MonadDB track; mirror dormant)

Same config as F4. `--validate-flat-state` NOT passed, so the flat-state mirror is dormant and the
path is identical to F4 (the regression check for the guarded hot-path edits). 3 reps:

| rep | wall | tps | gps | cmt median | cmt p99 | cmt max | slow >500ms |
|-----|------|-----|-----|-----------|---------|---------|-------------|
| 1 | 359s | 5697 | 505M | 12484µs | 24171µs | 90856µs | 0 |
| 2 | 338s | 6051 | 537M | 12445µs | 23722µs | 366064µs | 0 |
| 3 | 354s | 5777 | 513M | 12508µs | 24315µs | 43527µs | 0 |
| **median** | **354s** | **5777** | **513M** | **12484µs** | **24171µs** | — | **0** |

Within <1% of F4 on every metric — **no regression**. (These overwrote the F4 `/tmp` logs, hence F4's
numbers above are the only surviving record.)

**Shadow validation (the F5 gate) — PASSED.** A `-DMONAD_ENABLE_ROCKSDB=ON` build run with
`--validate-flat-state`, 3 reps over the same 10k blocks (commit `68b259338`), **finished cleanly
with zero assert aborts** — flat==trie held for every mirrored write across the replay, validating
the flat encoding/keying (account = `encode_account_db`; storage slot-keyed + incarnation;
one-directional check). The shadow adds the expected validation overhead (an extra RocksDB write per
commit + a shadow read+assert per state read), so these are NOT a production number:

| | wall | tps | gps | cmt median | cmt p99 |
|---|---|---|---|---|---|
| no-flag (MonadDB) | 354s | 5777 | 513M | 12484µs | 24171µs |
| shadow (median of 3) | 412s | 4964 | 440M | 16285µs | 32295µs |
| Δ (validation overhead) | +16% | −14% | −14% | +30% | +34% |

Overhead is the validation cost of a debug-only path, not a regression of the production path (the
real RocksDbDb perf is F9+); the no-flag MonadDB track stays flat. Also verified on the dev box:
the full ON build is clean and `test_kv_store` (6) + `test_db_parity_harness` (2) pass.

A later re-run (commit `2dbce2d7c`, 3 reps) reproduced the shadow result identically — clean finish,
no divergence, median 412s / tps 4964 / gps 440M.

### F9 — commit `31bd75d29`, MonadDB regression check (validating-flat shadow)

F9 adds the `RocksDbDb` backend and reworks `cmd/monad/main.cpp` into a backend-aware driver
(`raw_db`/`triedb` become TrieDb-only pointers; genesis load + block-hash seeding go through the
neutral `Db`). Because that touches the shared replay driver, the gate here is **no regression to the
MonadDB path**. Same config as F5 (nb=10000 from 22,830,000), `-DMONAD_ENABLE_ROCKSDB=ON`, run with
`--validate-flat-state` (so it's comparable to the F5 *shadow* row, not the no-flag row). Backend is
still `--state-backend=triedb` (default) — this run does **not** exercise RocksDbDb. 3 reps, clean
tree (`git diff` cksum empty):

| rep | wall | tps | gps | slow commits >500ms |
|-----|------|-----|-----|---------------------|
| 1 | 414s | 4940 | 438M | 0 |
| 2 | 398s | 5138 | 456M | 0 |
| 3 | 410s | 4988 | 443M | 0 |
| **median** | **410s** | **4988** | **443M** | **0** |

**No regression.** Median 410s vs the F5 shadow's 412s (<1%); `flat==trie` held for every write across
all 3 reps (zero assert aborts). The main.cpp driver refactor preserves both correctness and
performance on the MonadDB path; for `--state-backend=triedb` the new `is_triedb` branches resolve to
the original path.

**RocksDbDb perf (the real F9 number) — not yet run.** RocksDbDb is validated for *correctness* by
`test_db_rocksdb_parity` (in-memory MonadDB vs RocksDbDb agree on all four roots + sampled reads
across inserts/updates/storage-churn/deletion/incarnation-bump/code). A wall-clock number needs
`replay_rocksdb.sh` (bounded genesis replay, `--state-backend=rocksdb`); expect higher commit latency
than MonadDB (synchronous WAL per block), recovered by F10 (async write-back) + F11 (`async_io`).

### F9 — first real RocksDbDb replay (commit `482bb6c6c`, UNTUNED baseline)

Seeded the full mainnet state at block 22,830,000 from the filesystem snapshot
(`monad-rocksdb-seed`, streaming on-disk build), then replayed 10,000 blocks
(22,830,001 → 22,840,000) with `--state-backend=rocksdb`. Same block range as the
MonadDB track.

- **Seed:** 8h09m wall, store = **382 GB**, peak RSS 76 GB. Gate **passed** — the
  folded `state_root` (`0xe192ee2e…99869`) matched the snapshot's ETH_HEADER, so
  the conversion is correct.
- **Replay:** 7235 s, **282 tps**, 25 M gps, 2,045,301 tx.

| metric | RocksDbDb (untuned F9) | MonadDB |
|---|---|---|
| wall (10k blocks) | 7235 s | ~410 s |
| tps | 282 | ~5000 |
| commit median | 568 ms | ~12 ms |
| commit mean / p90 / max | 682 ms / 1.15 s / 8.8 s | — |
| slow commits >500ms | 6221 / 9913 | 0 |

**~18× slower, and it's all commit.** `txe` (execution) is ~20–50 ms/block; `cmt`
dominates. Root cause (confirmed against reth, which keys trie nodes by **path**
and range-scans changed subtrees): our `CF_TRIE_NODES` is keyed by **node hash**,
so each block's root walk does thousands of random point reads with no locality,
against a 382 GB store opened with **default RocksDB options** (~8 MB block cache,
no bloom filters) + a synchronous WAL fsync per block. reth's flat-state reads
match ours; the divergence is entirely the hash-keyed witness-walk root path.

**Tier-1 tuning (commit `8384ce1ee`)** lands on top of this: shared block cache
(`MONAD_ROCKSDB_BLOCK_CACHE_MB`, 32 GB in the replay script) + bloom filters +
pinned index/filter, a ~1M-node LRU, and async WAL. These are runtime options, so
the existing 382 GB store benefits on reopen with no re-seed. Tuned number pending
a re-run; the deep fix (path-based node keying, the reth approach) is Tier-2.
