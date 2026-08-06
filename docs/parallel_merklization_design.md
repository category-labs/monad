# Parallel merklization — design

> Worker threads merklize disjoint *new* subtries in memory; the triedb service
> thread serializes the results and closes the top levels. Enabled only for the
> snapshot restore path.
>
> `file:line` references are against `1fe408daa`; if they drift, grep the cited
> symbol.

## Goal / non-goals

**Goal.** Remove the single-core merklization ceiling from `monad-cli
--load-binary-snapshot`. The commit below this one ("Parallelize snapshot restore
across CPU cores") parallelized snapshot *prep* — file read, BLAKE3 verify, RLP
decode, key keccak — and measured 1.31×. The residual is the serial `db.upsert`,
and merklization is the bulk of it. That is what this design attacks: the
"Phase 2" the prep work deferred. Measured 1.60× alone, and 2.66× with prep.

**Non-goals.**

- **Not** parallelizing the writer. Node serialization, disk-offset assignment
  and `db_metadata` mutation stay on the single triedb service thread. Two prior
  attempts (`max/parallel-snapshot-threaded`,
  `dev/max/parallel-snapshot-restore`) tried a thread-safe shared node writer
  and drowned in deadlocks; the writer is a pipeline stage here, not a
  contended resource.
- **Not** enabling this for block execution. `upsert_concurrency` defaults to 0
  and the hook is inert unless a caller opts in. Only the snapshot loader does.
- **Not** changing the snapshot format, the wire, or the dump side.
- **Not** stacking on the page-groups chain (#2463/#2464) — see Rollout for why
  that one is now a conflict rather than a free composition. It *does* stack on
  parallel prep, which sits directly beneath it here; the two were developed
  independently off `origin/main` and each still measures on its own.

## Background

`commit_prepared` (`db_snapshot.cpp:598`) assembles a `finalized/{state,code}`
update tree from one prepared shard and calls `db.upsert(root, …, block,
false /*compaction*/, false /*can_write_to_fast*/)`. `Db::upsert` submits a
`FiberUpsertRequest` to the single triedb service thread and blocks the caller
on `fut.get()` (`db.cpp:865-872`). Everything below runs on that one thread, and
that blocking `get` is why the loader and the service thread cannot overlap
without the prep pipeline beneath this commit.

The recursion is `upsert()` (`trie.cpp:184`) → `upsert_` → `dispatch_updates_impl_`,
descending old trie and update list in lockstep. Nodes are built bottom-up:
`create_node_from_children_if_any` writes each child to disk to obtain its
offset, then `create_node_with_children` (`node.cpp:621`) allocates the parent
with those offsets and the merkle hashes baked in.

Four structural facts make the split possible.

**Merkle hashes do not depend on disk offsets.** `ChildData::finalize`
(`node.cpp:470`) sets `ptr`, `data` (the hash), `len`, `cache_node` and
`subtrie_min_version`; none of them read an offset. Only `ChildData::offset` and
`ChildData::min_offsets` come from writing. `make_node` copies them into
`child_fnext_data()` / `child_min_offset_{fast,slow}_data()`, which are plain
writable arrays in the node image — patchable after the fact.

**The in-memory `UpdateAux` already suppresses writing.**
`create_node_from_children_if_any` guards its whole write-and-evict loop on
`aux.is_on_disk()`. A subtrie built against a default `UpdateAux` therefore comes
out fully resident with every child offset `INVALID_OFFSET` — exactly the handoff
shape a worker needs, with no new gate in the recursion.

**Restoring into an empty database only ever creates.** A flush upserts account
hashes that do not exist yet, so the whole thing is built by `create_new_trie_` /
`create_new_trie_from_requests_`. No worker ever has to read an old node, and no
worker does I/O at all.

**Update sublists are counted.** `Requests::sublists` are
`boost::intrusive::slist` with constant-time size (16 bytes per list in the
352-byte `Requests`), so a frame can price a child's subtree in O(1) before
deciding whether to hand it over.

## Design

### Dataflow

```
service thread                                worker (or a helping thread)
  create_new_trie_from_requests_
    per branch whose sublist is large:
      submit{&children[i],                  ──►  create_new_trie_ against a
             updates_sublist,                     private in-memory UpdateAux:
             sm.clone(), prefix_index}            nothing written, every node
      wait(batch)   ← runs queued work           retained, offsets invalid
                                                 …splitting again wherever its
                                                 own sublists are still large
                                            ◄──  ChildData + post-order write
      per partition: retire_partition_             list + subtrie version
        → async_write_node_set_spare
        → patch fnext / min_offsets
        → drop uncached node pointers
    create_node_from_children_if_any()             ← unchanged
```

Partitions are cut and joined by one recursion frame — a fork-join, not an
asynchronous completion. That keeps `UpdateTNode::npending`
(`upward_tnode.hpp:56`) a plain `uint8_t` needing no atomics, and leaves
`upward_update` / `fillin_entry` / `create_node_compute_data_possibly_async`
untouched. Driving `child_done()` from worker threads is what sank
`max/parallel-snapshot-threaded`.

### Which subtries become partitions

A child is handed to a worker when its update sublist holds at least
`partition_min_updates` entries, and the machine says the table can be
partitioned at all:

```cpp
// StateMachine
virtual bool subtries_are_partitionable() const { return false; }

// MachineBase: the two tables keyed by a hash. The others are shallow, and the
// variable-length ones would have to be proven safe to merklize out of order.
bool MachineBase::subtries_are_partitionable() const
{
    return depth >= prefix_len() &&
           (table == TableType::State || table == TableType::Code);
}
```

Size, not depth, for three reasons that a depth window cannot cover:

- **A partition is never trivially small.** An earlier version of this design
  bounded partitioning to a window of nibbles past the table prefix. Measured on
  the restore integration test, that produced **38 947 partitions for 72 341
  nodes** — under two nodes each — and made the test 4× slower. Depth cannot
  express "is this subtree worth a handoff": the loader flushes per shard, so
  path compression puts equivalent work at depth 4 in one upsert and at depth 2
  in another.
- **Nesting terminates on its own.** Each level divides a sublist by up to 16,
  so a partition stops splitting after `log16(N/K)` levels with no explicit
  ceiling.
- **Whale contracts are broken up.** A whale is a *single* account-level update,
  so no account-level criterion — size or depth — would split it. But its
  *slot* sublists are enormous, and the frames inside its storage trie are still
  `subtries_are_partitionable()`, so the storage trie is partitioned. This is
  what bounds skew, and it is the thing the depth window got structurally wrong.

`partition_min_updates` is load-dependent, because it is measured against one
flush. A mainnet shard carries ~200k entries, so sublists at the first
divergence frame are ~12 500 and the default of 1024 splits them; the restore
integration test carries a few hundred accounts per flush, where sublists top out
at 166 and a mainnet-scale threshold would silently partition nothing at all.
The test therefore sets its own low threshold, and says why.

### Waiting helps

`wait()` runs queued partitions itself rather than idling, blocking only when the
queue is empty:

```cpp
while (batch.remaining_ != 0) {
    if (try_run_one()) { continue; }
    std::unique_lock g(lock_);
    cv_.wait(g, [&]{ return batch.remaining_ == 0 || !queue_.empty(); });
}
```

This is what makes nested partitions safe. A thread only parks when there is
nothing to help with, so work its own batch depends on can always be picked up by
somebody; and one condition variable serves both "work arrived" and "batch
finished", because a thread parked in `wait()` must wake for either. With two
condition variables, nested partitions could sit in the queue with every thread
parked on the wrong one.

It also puts the service thread to work instead of idling through the join, which
is where the earlier version of this design lost most of its winnings.

**"Only parks when the queue is empty" is not the same as "the workers are busy",
and in practice they are mostly idle.** Instrumenting the pool over a mainnet
restore at 16 workers (32 839 partitions) measures:

| | |
|---|---|
| partitions run by a parked-and-woken worker | 15 862 (48%) |
| partitions run by a thread *helping* inside `wait()` | 16 977 (52%) |
| wall time the queue held unclaimed work | 7.4 s of 128 s (5.8%) |
| **time work sat queued while any thread was asleep** | **0.12 s (0.09%)** |
| park events | 7 617 |

So helping carries over half the work, and the pool is starved rather than
blocked: there is nothing to help with 94% of the time, because the sole producer
of partitions is the service thread and it is itself the serialized critical
path. That is why pool occupancy is ~11% and no worker is near 100% CPU — which
is a throughput statement about the producer, not a contradiction of this section.

The 0.12 s figure is what rules out a lost wakeup, and a check made *before*
sleeping could not: `cv_.wait(g, pred)` evaluates the predicate first, so parking
while work is visible is impossible by construction, but a thread that parks and
is then missed by a `notify` would be invisible to that argument. Spread over
7 617 parks the 0.12 s is 16 µs each, i.e. bare futex wake-and-schedule latency,
so every push does reach a thread. Work arrives in bursts — depth peaks at 1 265
against a mean of 7.7 — and is drained fast.

Consequence to be aware of: helping nests recursion on the helper's stack —
`wait()` → `try_run_one()` → `build_partition_subtrie` → `create_new_trie_` →
`wait()`. The queue is LIFO, so a thread overwhelmingly helps with its own
descendants and the nesting is bounded by the partition-tree depth
(`log16(N/K)`, three or four in practice) times the trie recursion, comfortably
inside a default 8 MB stack.

### Writing the finished subtrie

The worker records, in post-order, every descendant it built:

```cpp
struct PendingWrite { Node *node; Node *parent; uint8_t index; bool evict; };
```

and the service thread's retirement is a flat loop over that list: allocate an
offset with `async_write_node_set_spare`, patch `child_fnext_data()[i]` and
`child_min_offset_{fast,slow}_data()[i]` from `calc_min_offsets`, and drop the
pointer if `evict`. Post-order matters twice: a child's min-offset array is final
before its parent's entry is computed, and a node's `fnext` array is patched
before the node image itself is serialized.

The walk itself — stepping the StateMachine nibble by nibble to evaluate
`sm.cache()` at each child's own depth — is the expensive part, and it belongs on
the worker. An earlier version had the service thread walk the subtrie, and
profiling put `MachineBase::down` at **41.5%** of that thread with the walk's own
frame at another 18.8%: over 60% of the residual was a walk whose only output was
one bit per child. Computing `evict` on the worker also avoids assuming
`cache()` is monotone in depth, which a depth-cutoff shortcut would have needed.

The partition root's own offset is deliberately *not* assigned here — the
`child.offset == INVALID_OFFSET` arm of the parent's
`create_node_from_children_if_any` still does that, exactly as for a serially
built child.

### The `Compute` race

`MachineBase::get_compute()` (`util.cpp:455`) returned function-local `static`
`Compute` objects, and `MerkleComputeBase` carries mutable
`detail::InternalMerkleState` from `compute_node_data_len` to the matching
`set_node_data` (`compute.hpp:36`, `:137-194`). Concurrent merklization through
one instance interleaves those calls and produces wrong hashes.

Fix: `thread_local` on the 15 statics across `get_compute`, `storage_compute`,
`storage_root_compute` and the two Monad overrides. Giving each Machine its own
Compute set instead would break `static_assert(sizeof(MachineBase) == 16)` and
every `clone()`, and the TLS guard load is negligible against a keccak.

The state is only written for a node that has *both* a value and children — an
account with storage — so a workload without nested tries hides the bug
entirely, and so does a storage-only compute (slot leaves are terminal).
`parallel_upsert_test` is built around that: reverting the `thread_local` fails
9 of its cases, including at one worker, since the service thread helps and so
merklizes concurrently too.

### Ordering and safety

- **Partitions are disjoint** and are built purely from the update list, so no
  two threads touch the same subtree and none reads what the writer is emitting.
- **A worker performs no I/O and touches no shared trie state.** Its in-memory
  aux has no `AsyncIO`, no `metadata_ctx_`, no node writers, and default
  compaction state. The only objects it mutates are its own `sm` clone, its own
  `ChildData`, its own write list, and the `Update` objects of its own sublist
  (which `Requests::split_into_sublists` has already partitioned by branch).
- **`Node::SharedPtr` is `std::shared_ptr`**, and the trie/node allocators are
  stateless wrappers over `malloc` / `operator new`, so building nodes on one
  thread and releasing them on another is safe.
- **Waiting never polls the caller's `AsyncIO`**, so a batch cannot be joined
  from inside one of the caller's own I/O completions.
- `DbAsyncWorker` refuses to combine concurrency with compaction: a worker never
  compacts, and retirement skips the compaction assertions the serial write loop
  makes.

### Restore wiring

- `OnDiskDbConfig` gains `unsigned upsert_concurrency{0}` and
  `uint32_t partition_min_updates{1024}`. 0 concurrency means the context is
  never constructed and `UpdateAux::parallel()` stays null.
- Only the snapshot loader opts in, via `monad_db_snapshot_loader_create` /
  `monad_db_snapshot_load_filesystem` and the `monad-cli --upsert-concurrency` /
  `--partition-min-updates` flags.

## Measured

### Where the time goes, serial

`category/execution/ethereum/test/test_restore_profile.cpp` builds a source db,
dumps a snapshot, and restores it as two `DISABLED_` cases so `perf` can be
pointed at the restore alone.

At mainnet scale (block 90045827, 11 GB, 256 shards, NVMe-backed LV), the serial
restore runs at **104% total CPU** — which is *not* "mostly blocked". Per-thread
accounting shows two threads that are **strictly serialized**, because the loader
blocks in `db.upsert` while the service thread has nothing else queued:

| thread | CPU | share of wall |
|---|---|---|
| triedb service thread | 157.6 s | 73% |
| loader (read, blake3, RLP decode, key keccak) | 53.8 s | 25% |
| QuillBackend / io_uring worker | 8.0 s | 4% |

158 + 54 ≈ the 215 s wall. Two consequences: the restore's wall clock is simply
their sum, so **pipelining the loader against the upsert is worth ~1.3× by
itself** — which is what the Phase-1 branch measured, now with a mechanism rather
than an Amdahl fit — and anything done to the service thread is capped by the
54 s of loader work that remains.

Within the service thread (percentages of the whole process; divide by 0.731 for
share-of-thread):

| bucket | % process | % of thread |
|---|---|---|
| `__KeccakF1600` | 24.26 | 33.2 |
| `MachineBase::down` | 11.77 | 16.1 |
| `create_new_trie_` | 5.19 | 7.1 |
| `encode_two_pieces` | 4.45 | 6.1 |
| `poll_uring_` (+lambdas) | 2.77 | 3.8 |
| `Requests::split_into_sublists` | 2.71 | 3.7 |
| `rlp::parse_list_metadata` | 2.28 | 3.1 |

**The step-0 profile's "28.4% uring ceiling, unexplained" was an artifact of a
50 MB snapshot on an LVM-backed file.** At mainnet scale `poll_uring_` is 3.8%
and the thread is doing merklization, which is exactly the work that can move.
(3.8% is the *polling*, not the write path as a whole; once merklization moves
off, the write path is a much larger share of a much smaller residual — see
"Where the time goes, merklization parallel".)
(Whole-process keccak is 41.22% = 24.26 service + 16.95 loader, which is how the
per-thread filtering above was validated.)

### Result

Mainnet, slot target. Every run's state root equals the `state_root` in the
snapshot's own block-90045827 eth_header, so correctness has an absolute oracle
here rather than a self-comparison.

| workers | `partition_min_updates` | wall | vs serial | total CPU | peak RSS | partitions |
|---|---|---|---|---|---|---|
| 0 | — | 214.96 s | 1.00× | 104% | 6.74 GiB | — |
| 16 | 64 | **134.40 s** | **1.60×** | 268% | 9.59 GiB | 1 299 178 |
| 16 | 1024 | 134.99 s | 1.59× | 257% | 9.58 GiB | 32 839 |
| 16 | 16384 | 171.21 s | 1.26× | 152% | 9.63 GiB | 1 459 |
| 32 | 1024 | 136.69 s | 1.57× | 278% | 9.61 GiB | 32 839 |

### Speedup against worker count

A separate sweep, one binary, `partition_min_updates` 1024 throughout, same
oracle on every run:

| workers | wall | speedup | total CPU | utilisation | peak RSS |
|---|---|---|---|---|---|
| serial | 215.75 s | 1.00× | 225 s | 104% | 6.74 GiB |
| 2 | 167.44 s | 1.29× | 304 s | 181% | 9.62 GiB |
| 3 | 153.21 s | 1.41× | 305 s | 199% | 9.60 GiB |
| 4 | 144.27 s | **1.50×** | 308 s | 213% | 9.60 GiB |
| 5 | 142.29 s | 1.52× | 314 s | 220% | 9.60 GiB |
| 6 | 140.09 s | 1.54× | 322 s | 230% | 9.63 GiB |
| 7 | 136.21 s | 1.58× | 326 s | 239% | 9.59 GiB |
| 8 | 136.11 s | 1.59× | 330 s | 242% | 9.59 GiB |
| 16 | 127.99 s | 1.69× | 342 s | 266% | 9.58 GiB |

The knee is at **four workers** (1.50× for +37% CPU); 4→8 adds 0.09× and 8→16
another 0.10×. Run-to-run variance is about 5% — this sweep puts 16 workers at
128.0 s where the sweep above gives 135.0 s — so the 5/6/7/8 points are one
plateau, not a trend. Peak RSS is a step rather than a slope: it jumps the moment
any worker exists and is then flat, because it is set by the subtries held in
flight, not by thread count.

32 workers do not beat 16, which is the signature of the writer being the
bottleneck again. K=64 and K=1024 tie on wall clock despite 40× the partition
count, so 1024 is the better default: same speed, far less bookkeeping.

On the synthetic harness (1M accounts, 50 MB, per-shard flushes so sublists are
~244), the plateau is K=32–128 at 2065–2275 ms against 3168 ms serial ≈ 1.5×,
with ±10% run-to-run noise. K=2 over-partitions (745 874 partitions, 0.91×) and
K≥1024 exceeds the workload's sublists and partitions almost nothing.

### What the two fixes were worth

The first working version of this design used a per-node fork-join with no
helping and had the service thread walk each finished subtrie. It measured
**1.10×** at mainnet scale with peak RSS 14.98 GiB. Per-thread accounting showed
why: the offload itself worked (service thread 167.6 s → 74.4 s) but the thread
then sat **idle ~64 s, 46% of the upsert phase**, blocked on barriers, with
worker occupancy at 1.3 cores of 16. Replacing the barrier with size-based
partitions plus a helping `wait()`, and moving the walk to the worker, took that
to 1.60× and cut the memory regression from +8.2 GiB to +2.9 GiB.

### Where the time goes, merklization parallel

The profile above is the *serial* one, and it stops describing the run the moment
this design is switched on, so the sweep's flattening at four workers must not be
read off it. Re-profiled at 16 workers, wall 130.4 s (flat `perf` profile: this
machine is AMD, so no LBR, and the gcc-avx2 toolchain omits frame pointers, so
self time only — no call graphs):

| thread | CPU | share of wall |
|---|---|---|
| loader | 56.4 s | 43% |
| triedb service thread | 55.5 s | 43% |
| 16 merklization workers | 221.6 s total | 10.6% pool occupancy |

Merklization has left the service thread as intended — 157.6 s → 55.5 s — but the
loader did not shrink, so **the two are now co-equal halves of the same serialized
chain**: 56.4 + 55.5 ≈ the wall, the remainder being startup and the final root
write. Nothing is saturated; the job uses ~2.6 of 128 cores.

Service thread residual:

| bucket | % of thread | seconds |
|---|---|---|
| write path (offset allocation, `fnext`/min-offset patching, serialize) | 28.0 | 15.5 |
| io_uring + block layer | 19.1 | 10.6 |
| malloc/free | 15.1 | 8.4 |
| merklization that never partitioned | 12.8 | 7.1 |
| keccak | 5.6 | 3.1 |

The loader, meanwhile, is **64% keccak** (36.2 s) plus 3% blake3: one
`keccak256(address)` per account and one per slot key, with no db dependency at
all.

So the write path is 15.5 s of a 130 s wall — **perfecting it is worth ~1.13×**,
whereas overlapping a loader that is two thirds independent hashing is worth far
more. The serial profile cannot be used to rank those two, because the thing it
shows dominating is the thing this design removes; the ranking has to be read off
a parallel profile.

### Combined with parallel prep

Phase 1 — parallel per-shard prep feeding a bounded queue whose consumer commits —
is the commit below this one on this branch, so the combination is measurable.
One binary, mainnet, slot target, warm page cache, every row checked against the
eth_header oracle:

| `--load-concurrency` | `--upsert-concurrency` | wall | vs serial | CPU | peak RSS |
|---|---|---|---|---|---|
| 1 | off | 212.9 s | 1.00× | 105% | 6.50 GB |
| auto (16) | off | 162.3 s | 1.31× | 142% | 14.31 GB |
| 1 | 16 | 131.2 s | 1.62× | 262% | 9.45 GB |
| auto (16) | 16 | **80.1 s** | **2.66×** | 448% | 16.69 GB |

1.31 × 1.62 = 2.12, so the combination is **better than multiplicative**, and the
serialization is exactly why: `Db::upsert` blocks its caller on a promise, so time
taken out of either half exposes the other instead of merely adding to it.

The cost is resident memory, 6.50 → 16.69 GB, and it is mostly Phase 1 holding
each in-flight shard whole (14.31 GB on its own) rather than this design's
in-flight subtries.

### Thread budget

The two features size their pools differently, which matters because the fleet's
ordinary machine is a 16-core Ryzen, not the 64-core part these numbers were taken
on.

- Prep is **auto by default**: `min(hardware_concurrency(), 16)`, one dedicated
  producer plus a `tbb::task_arena` the producer masters. The queue capacity is
  also the worker count, so it bounds resident shards, which is what actually
  costs memory.
- Merklization is **off unless asked** and then takes exactly the count given,
  with no cap; the service thread helps via `wait()`, so effective width is
  `workers + 1`.
- Both on at 16 is ~34 threads.

Measured on a 16-core / 32-thread Ryzen 9 7950X against a 2.5 GB snapshot, same
oracle on every row:

| load / upsert | wall | vs serial | mean cores | peak cores | peak RSS |
|---|---|---|---|---|---|
| 1 / off | 55.5 s | 1.00× | 1.10 | 1.3 | 4.98 GiB |
| auto / off | 42.4 s | 1.31× | 1.36 | 2.4 | 7.14 GiB |
| 4 / 4 | 28.3 s | 1.96× | 2.62 | 4.6 | 6.96 GiB |
| 8 / 8 | 26.3 s | 2.11× | 2.90 | 5.0 | 7.29 GiB |
| auto (16) / 16 | **24.3 s** | **2.28×** | 3.51 | 6.9 | 7.90 GiB |

**34 threads on 16 cores costs nothing: peak demand was 6.9 cores of 16.** The
pools are latency-oriented and mostly idle, so a thread count above the core count
is not oversubscription in any harmful sense. **More workers stays monotonically
better even there** — 16/16 beats 8/8 beats 4/4 — so the sweep's knee at four is
a statement about diminishing returns, not a reason to shrink the pool on smaller
hardware. Returns do flatten: 8 → 16 buys 7.6%. Resident memory grows much less at
this scale (+58% rather than +157%) because it tracks shard size; worker count
adds only ~1 GiB.

### Remaining headroom

**The write path is the ceiling, but only now that the loader is pipelined.** In
the combined run the service thread is 50.6 s of the 80.1 s wall and is the
dominant thread, which puts the write path at ~14 s of 80 s ≈ 1.2×. Serialization
into the node writer and offset allocation are single threaded by this design's
own non-goal, so this is the next real change rather than more merklization
concurrency.

Two cheaper things are visible in the same profile:

- **8.4 s of malloc/free on the service thread** is it releasing the nodes the
  workers built, and that cost is created by this design rather than inherited.
  Process-wide allocator time goes from 2.6 s serial to 14.7 s here — `_int_free`
  2.14 → 8.43 s, `_int_malloc` 0.41 → 4.65 s, and `unlink_chunk` 0.07 → 1.58 s,
  a 23× jump that is the signature of bulk-freeing cold chunks — with more than
  half of it landing on the critical path. The cause is structural: a worker
  suppresses the write-and-evict loop, so a whole subtrie is allocated on one
  thread and then freed on another in one go, instead of each node being written
  and evicted as the serial recursion reaches it. Freeing on the worker, or an
  arena per partition, recovers most of it — over half of what perfecting the
  entire write path would give, for far less work.

For contrast, the **dispatch itself is free**: `submit` is 0.20% of the service
thread and locks, futex and scheduling together another 0.03%, so handing 32 839
partitions to the pool costs it about 0.13 s. `split_into_sublists` is not part of
that — the serial recursion splits by branch too, and process-wide it grows only
6.1 → 9.8 s. Whatever the handoff costs, it is not the splitting.
- `MachineBase::down`, one virtual call per nibble, 16% of the serial service
  thread and still 7.8% of the parallel one.

## Testing

- **`category/mpt/test/parallel_upsert_test.cpp`.** The same updates through an
  in-memory serial trie and through an on-disk trie at
  `workers ∈ {1,2,8}` × `partition_min_updates ∈ {2, 1000, 100000}` — splitting
  at every opportunity, splitting only the top levels, and not splitting at all.
  Asserts an identical root hash, then reads every key and nested key back from
  disk. Disk offsets legitimately differ (write order differs), so the assertion
  is on trie content, not layout. Three shapes: plain, every key sharing an
  8-nibble prefix so the cut falls inside a shared path, and two sequential
  upserts so the service thread reads old nodes back while workers run.
- **`DbBinarySnapshot.ParallelMerklizationMatchesSerial`.** End to end through
  the real `OnDiskMachine` / `MonadOnDiskMachine`: dump, then restore four
  times — slot target serial and parallel (both must equal the source root), and
  page target serial and parallel (equal to each other; page and slot encodings
  hash differently by design). Each restore also reads accounts and storage
  slots back.
- **`DbBinarySnapshot.ParallelLoadMatchesSerialSlot`** additionally loads with
  parallel prep *and* partitioned merklization at once and asserts the same root.
  The two features meet on the same load from opposite ends, so neither feature's
  own test covers the pair. Its page counterpart deliberately does *not* do this:
  that fixture has one account per shard and page encoding collapses an account's
  slots into a single leaf, so no sublist can ever reach the threshold and the
  assertion would pass without partitioning anything.
- **Verified by injection, not merely by passing.** Reverting one `thread_local`
  compute fails 9 mpt cases. Dropping the `set_fnext` patch aborts both suites —
  though note it only aborts the integration test *because* that test reads
  leaves back: a root hash is independent of child offsets, so the earlier
  root-hash-only version of that test passed with the write path broken.
  Asserting inside the submit branch fires in both suites, so both really do
  partition — and it is what proved the page case above does not.

## Rollout

Inert at `upsert_concurrency = 0`, which is every caller except the snapshot
loader when explicitly asked. Prep, by contrast, is on by default, so landing the
two together changes default behaviour where landing this one alone would not.

**Interaction with the snapshot-framing chain (#2463 ← #2464).** This is no longer
just a tuning note. Parallel prep **deletes the loader's byte-counted flushing
outright** — `bytes_read` and `BYTES_READ_BEFORE_FLUSH` go with it — because a
prepared shard is committed in exactly one `db.upsert`. #2464 works the other way,
lowering that threshold from 10 GiB to 1 GiB and adding flushes at page-group
boundaries to bound memory. The two therefore collide structurally in
`db_snapshot.cpp` rather than merely needing `partition_min_updates` re-tuned, and
whichever lands second has to reconcile them. Worth weighing against the resident
memory the combination costs: #2464 exists to bound exactly the whole-shard
buffering that prep makes worse.
