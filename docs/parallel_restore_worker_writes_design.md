# Worker-side node writes for parallel restore — design

> Each merklization worker gets a reserved byte range in the current chunk of
> the upsert's target list (the slow list for a restore) and an 8 MB buffer,
> runs the ordinary write-and-evict recursion against it, and
> `pwrite`s the buffer itself. Node serialization, disk-offset assignment and
> node freeing leave the triedb service thread. Enabled only for the snapshot
> restore path.
>
> `file:line` references are against `34c374ec6`, the commit this was designed
> against, except where a section says otherwise. Line numbers drift; grep the
> cited symbol.

## Goal / non-goals

**Goal.** Take the write path and the allocator off the triedb service thread,
which parallel-restore profiling identifies as the remaining ceiling. Two
different runs supply that picture, and they must not be conflated:

- *Where the wall goes*: in the **both-on** run (80.1 s wall) the service thread
  is busy 50.6 s — 63% duty — and is the dominant single thread.
- *Where the service thread's time goes*: the only per-symbol profile of the
  pre-change code is `par16_flat_2026-08-04.data`, which is the
  **merklization-only** run (131.2 s wall, service thread 55.4 s). There the write
  path (offset allocation, `fnext`/`min_offset` patching, serialization) is 25.2%
  ≈ 13.9 s and `malloc`/`free` is 14.2% ≈ 7.9 s.

Both are per-node costs that belong wherever the node was built. The shares come
from the merklization-only run and the wall from the both-on run, so any "N
seconds of the service thread" figure below that mixes them is an estimate, not a
measurement.

**Non-goals.**

- **Not** enabling worker writes for block execution. They exist only behind
  `--upsert-concurrency`, which only the snapshot loader sets.
- **Not** an arena that doubles as the write buffer. Nodes stay
  `malloc`-allocated; only *where* they are serialized and freed changes. In-place
  construction founders on `Node`'s memory-only `next` SharedPtr tail
  (`node.hpp:169-186`), which is inside the allocation but outside the disk image,
  and on `allocate_shared`'s inline control block: neither leaves room for the
  4-byte size prefix at the alignment the format needs.
- **Not** reducing total CPU against a *serial* restore: it rises there, 228 →
  274 core-seconds (**1.20×**), and that extra 20% is what parallelizing costs.
  The run averages 8.65 cores over its 31.7 s wall. Deliberately no "parallel
  efficiency" figure: the job runs ~34 threads (16 prep, 16 merklization, the
  service thread, the loader's consumer) on a 128-core box, so there is no
  processor count to divide a speedup by, and quoting one invites the reader to
  assume a different denominator than the one used. CPU does fall against the
  write-list baseline this
  design replaces, ~359 → ~277 s, because dropping the write list also drops the
  separate `collect_partition_writes_` walk over the finished subtrie; see
  Measured. Peak measured demand was 6.9 of 16 cores, a **pre-change** figure
  from the 16-core box that has not been re-measured since.
- **Not** changing the snapshot format, the wire, or the dump side.

**Scope caveat.** The reservation change below is *not* restore-only. The service
thread's own writer submits through `AsyncIO::submit_request_`, so reserve-at-grant
is a shared-path change. It leaves live-execution behavior identical — same
offsets, same write order — and replaces a guard that cannot detect misplacement
with one that can.

## Background

This section describes the baseline this design replaces, as parallel
merklization first shipped it. That baseline is a state internal to this work,
not anything `main` ever had — on `main` restore is serial and there is no write
list at all. None of the names below survives in the tree; they are here because
the argument for the change is an argument about what they cost.

In that baseline a worker built its partition against an in-memory `UpdateAux`,
which suppressed writes because `create_node_from_children_if_any` gated its
write-and-evict loop on `aux.is_on_disk()`. The whole subtrie therefore stayed
resident, the worker recorded a post-order write list
(`collect_partition_writes_`), and the service thread replayed it flat in
`retire_partition_`:

```cpp
for (auto const &w : p.writes) {
    auto const offset = async_write_node_set_spare(aux, *w.node, true);
    auto const virtual_offset = aux.physical_to_virtual(offset);
    w.parent->set_fnext(w.index, offset);
    w.parent->set_min_offsets(w.index, calc_min_offsets(*w.node, virtual_offset));
    if (w.evict) {
        w.parent->set_next(w.index, nullptr);
    }
}
```

That loop was the whole cost. The last line dropped the only owning reference to
a node the worker allocated, so every eviction was a cross-thread cold free — the
23× `unlink_chunk` in the profile is that signature. The rest was the write path
itself.

The serial recursion already does exactly the same four things on the thread that
built the node (`create_node_from_children_if_any`). So the change is not to add
a mechanism but to stop suppressing the one that exists.

### Why offsets can be assigned locally

The recorded write list was post-order because a parent's `fnext` array is part
of its own disk image, so children must have offsets first. The create recursion
is already post-order for the same reason. Given a private byte range, a worker
can satisfy that ordering without consulting anybody: `physical_to_virtual`
(`update_aux.cpp:74-91`) reads only `atomic_load_chunk_info(..., acquire)` and an
`insertion_count` that is fixed once the chunk is on the fast or slow list, so
`min_offsets` is computable on the worker too.

Only the partition root crosses a thread boundary, and it always did: the root
node is written by the frame that cut the partition, from *that* thread's extent,
and `ChildData` carries the offset back as it does for any child.

## Design

### Reservation: split reserve from placement

`chunk_t::write_fd(bytes)` (`storage_pool.cpp:154-182`) already is an atomic
append-offset allocator: for an append-only chunk it `fetch_add`s
`chunk_bytes_used` and returns the pre-increment offset. What makes it unusable
as-is by more than one writer is that `AsyncIO::submit_request_`
(`io.cpp:444-455`) calls it *at submit time* and writes at the offset it returns,
checking the caller's intent only as:

```cpp
MONAD_ASSERT_PRINTF((chunk_and_offset.offset & 0xffff) == (offset & 0xffff), ...)
```

Sixteen bits. Every 8 MB extent boundary is `0` under that mask, so two writers
submitting out of order both pass and one lands in the other's range. The
corruption is silent until something reads a node written by the loser.

Therefore:

- `chunk_t::reserve(bytes) -> file_offset_t` — the existing `fetch_add`, named for
  what it does.
- `chunk_t::write_offset(chunk_relative) -> {fd, absolute}` — no `fetch_add`.
- A writer holds a reservation `[base, base + len)` and a replacement buffer is
  positioned at the next unwritten offset *inside* it; it reserves again only when
  the reservation is exhausted. `reset_node_writers` (`update_aux.cpp:474-486`),
  `replace_node_writer` and `replace_node_writer_to_start_at_new_chunk`
  (`trie.cpp:1561,1637`) are the three sites. Resuming inside the reservation is
  what keeps the live path waste-free: reserving afresh at every flush would
  orphan the unwritten tail of an 8 MB reservation once per block.
- `submit_request_` writes at the caller's offset and asserts
  `offset + size <= reservation cursor`, which is a check on placement rather
  than on the low bits of an address.

Two consequences of reserving ahead of writing, both accepted:

- `chunk_bytes_used` — which `chunk_t::size()` returns for a seq chunk, the same
  counter `reserved_bytes()` reads — stops meaning "bytes of valid data" while a
  triedb is open for writing; it is the allocator cursor and runs up to one
  reservation ahead of each writer. It is back in step at the next open, which
  trims it to the recorded offset. Three consequences for its readers:
  - Anything that appends with `write_fd` cannot assume a triedb it just opened
    left the append point alone. The `cli_tool` restore did, and now opens its
    scratch triedb read-only.
  - `Db::get_storage_stats` overstates by ≤ 8 MB per writer **on block devices
    only**: `device_t::capacity()` sums `chunk_bytes_used` there, while for a
    file-backed pool it reports `st_blocks` (`storage_pool.cpp:104-105`), and a
    reserved-but-unwritten tail is a hole that does not move the gauge.
  - `cli_tool --archive` copies `chunk.size()` bytes per chunk
    (`cli_tool_impl.cpp:489`, then `clone_contents_into`), so an archive taken by a
    process that also holds a writable triedb captures each writer's unwritten
    tail. Harmless — those bytes sit above the restored db's `start_of_wip` and are
    trimmed at its first open — but the archive is marginally larger.
- The exclusive end of a reservation is a chunk-relative byte count, not a
  `chunk_offset_t`: the last reservation in a chunk ends *at* `chunk_capacity`,
  and with the default 28-bit capacity that is one past `chunk_offset_t`'s
  28-bit offset field.

Out-of-order writes within a chunk are then fine on files and block devices. They
are not fine on genuinely zoned devices — but `write_fd` `MONAD_ABORT`s on zonefs
today (`storage_pool.cpp:181`), so this is a trade we are stating, not a contract
we are breaking silently.

### The worker writer

`WorkerNodeWriter`, one per worker **thread** — not per partition — in
`parallel_upsert.{hpp,cpp}`:

- Owns an `aligned_alloc(DISK_PAGE_SIZE, extent_bytes)` buffer for its
  lifetime: the pool's write fd is O_DIRECT against 512-byte blocks, and
  `DMA_PAGE_SIZE` (64) is too small an alignment for it. No registered-buffer
  pool, so `wr_buffers` stays at its default of 4 (`ondisk_db_config.hpp:37`).
- Holds a reserved range `[base, base + len)` in the target list's current
  chunk and a cursor. `append(Node const &)` serializes with
  `serialize_node_to_buffer` and returns the `chunk_offset_t`, with the
  `spare` page count set exactly as `async_write_node_set_spare` does
  (`trie.cpp:1826-1827`).
- When the node does not fit: pad the tail to `DISK_PAGE_SIZE` with `memset`,
  `pwrite` the buffer at `write_offset(base + flushed)`, and reserve the next
  extent. Blocking is deliberate — ~4 ms per 8 MB on NVMe, on a thread that is
  otherwise hashing.
- The extent is `min(AsyncIO::WRITE_BUFFER_SIZE, chunk_capacity / 32)`, i.e. 8 MB
  on a production 256 MB chunk and a proportionally smaller slice of a smaller
  one. A fraction has to bound it: with an extent that is a large part of a
  chunk, the first few writers each own a whole chunk and the free list empties
  long before any of them has filled what it holds. No CLI knob, but a test-only
  override on `ParallelUpsertContext`, for the same reason `set_flush_bytes` has
  one and no flag: at unit-test scale a production-sized extent means the
  boundary paths never execute.

A node larger than an extent gets its own reservation of
`round_up_align<DISK_PAGE_BITS>(disk_size)` and is written directly from the node
rather than through the buffer. Restore values top out far below 8 MB, but
`Node::max_disk_size` is 256 MB and an abort in that corner is not acceptable.

### Chunk grants

Every reservation takes `extent_lock_`: the remainder read and the reservation
that consumes it have to be one critical section, or two reservers racing the
same remainder would both clamp to it and both reserve it
(`ParallelUpsertContext::reserve_extent`). Crossing a chunk needs a free-list
pop and a `metadata_ctx().append`, which run under that same lock on whichever
thread exhausted the chunk — service thread or worker alike, not
service-thread-only. A worker whose reservation would exceed `chunk_capacity`
clamps to the 512-aligned remainder and requests the next chunk through the
context. At 256 MB per chunk that is ~44 grants for an 11 GB restore.

`advance_db_offsets_to` (`trie.cpp:1870`) then takes the reservation cursor rather
than the service writer's offset, since worker extents may sit ahead of it. Gaps
below the cursor — a worker's partly-used extent — are orphaned bytes; nothing
scans the region, every node is reached by a recorded offset. Two consequences:

- The recorded chunk must be the last of its list, because
  `rewind_to_match_offsets` (`update_aux.cpp:207-229`) *destroys* every chunk
  after it. The grant is therefore the sole appender of that list while a
  parallel upsert is in flight, and the cursor is always in the chunk it last
  granted. When that chunk is exactly full the cursor grants one more, since an
  offset of the capacity is one past `chunk_offset_t`'s 28-bit offset field and
  `try_trim_contents` cannot punch a zero-length hole at it either.
- The tail of a chunk the allocator has moved past is orphaned wholesale if the
  service thread's own writer still holds an extent in it, which it does whenever
  it writes slowly enough not to exhaust that extent. Bounded by one chunk per
  restore, and it is what
  `DbBinarySnapshot.CompactionAfterParallelRestore`'s pool sizing has to leave
  room for.

### Which writer a partition uses

`wait()` helps rather than idles, so a partition can run on any pool thread *or on
the service thread itself*. Writer selection is therefore by thread, not by
partition: a pool thread serializes into its own `WorkerNodeWriter`, and the
service thread keeps using `node_writer_fast`/`node_writer_slow` and the uring
path. Nested partitions inherit the same rule, so a subtrie can span two
writers — which is sound, because a child's offset is final before its parent is
serialized regardless of which extent it landed in.

A partition worker's aux has no node writers of its own, so a partition the
service thread picks up writes through `UpdateAux::writer_owner()`, the aux that
does. That aux is also the one whose `can_write_to_fast` and reservations apply,
which is what keeps those writes in the same chunk list the workers reserve from.

The service thread's writer for that list takes its buffer placement from the
allocator too, rather than from `chunk_t`'s append point: it shares the chunk, so
neither the append point nor the bytes past its own reservation are its to take.
A node that no longer fits inside that reservation therefore starts a fresh
extent instead of being split across one boundary
(`async_write_node`), because a node has to be contiguous on disk and the bytes
after the reservation belong to whoever reserves next.

### What the worker aux may touch

The worker's `UpdateAux` is constructed per partition, borrowing the submitter's
`AsyncIO` pointer, its `DbMetadataContext` and a copy of its per-timeline
compaction state, plus `set_parallel(&ctx)` so nested partitioning still fires. It
must report `is_on_disk()`, which is `io != nullptr` (`trie.hpp:374`); it reads
`chunk_capacity`, `chunk_count` and `storage_pool().chunk()` through the i/o
pointer, translates its own write offsets through the metadata, and checks its own
nodes against the compaction and auto-expire thresholds of the upsert that cut it.
Writes dispatch to the calling thread's writer at
the single site `async_write_node_set_spare`, so a pool thread never enters
`async_write_node`, whose first statement is
`aux.io->poll_nonblocking_if_not_within_completions(1)` (`trie.cpp:1690`).

That is a checked property rather than a convention: `AsyncIO` already records its
owning thread and asserts it unconditionally in `poll_uring_` (`io.cpp:531`),
which every `poll_*` entry point funnels through, and `make_connected` gains the
same check as a `MONAD_DEBUG_ASSERT` — debug only, because it is hot in live
execution.

`metadata_ctx` is read concurrently and only through `atomic_load_chunk_info`.
A worker *is* a mutator of it, though: the chunk grant runs on whichever thread
exhausted the chunk, so `remove`/`append` are no longer service-thread-only.
Three things keep that sound:

- Mutators are serialized against each other by `extent_lock_`, which the grant
  runs under. Every other `db_metadata` mutation an upsert makes — history
  trimming, `advance_db_offsets_to`, compaction — happens on the triedb's own
  thread with no partition in flight. The two places that could break that are
  `replace_node_writer` and `replace_node_writer_to_start_at_new_chunk`, which
  pop `free_list_end()` and `remove`/`append` it *without* `extent_lock_` on the
  branch taken when the allocator does not own that writer's list. Both assert
  `no_partitions_in_flight()` before the pop, so an unlocked pop that could race
  a worker's grant aborts rather than losing an update to the tail's
  `chunk_info_t` word.

  Two facts keep that assert from firing during a restore, and both are worth
  knowing before changing either: `db.cpp` asserts `!options.compaction`
  whenever `upsert_concurrency > 0`, and the loader upserts with
  `can_write_to_fast = false`, so the only writer the service thread advances is
  the one the allocator owns — which routes to the locked path instead. A
  configuration that advanced both writers with workers live would hit the
  assert, not the race.
- Readers on the *find* path are lock-free and atomic, so the append has to
  publish atomically to match. `append_` (`db_metadata.hpp`) stores the new
  chunk's whole word with `std::atomic_ref` release, and links it onto the
  previous tail the same way: that tail is exactly the chunk the workers are
  filling and translating offsets in, so a bitfield write there would be a data
  race, benign on x86-64 but visible to TSAN and not a thing to leave in.

  The service thread's own *write* path is not atomic in the same way. It reads
  `at(off.id)->in_fast_list` as a plain bitfield load at three sites — the two
  `replace_node_writer*` entry checks and the post-write cross-check in
  `async_write_node_set_spare`. When that chunk is the list tail, those loads race
  a worker's release store: the same benign-on-x86-64, TSAN-visible class as the
  race fixed on the writing side, and unfixed here.
- `remove` touches only the free list's own links, which no worker reads.

### Publication barrier

Worker buffers are flushed inside `flush_buffered_writes` (`trie.cpp:1831`),
before `advance_db_offsets_to` and before the root offset is appended in
`write_new_root_node` (`trie.cpp:1864-1878`). A completed O_DIRECT `pwrite` is as
durable as a completed uring write under the existing PLP-SSD assumption, so no
`fsync` enters the path and the crash story is unchanged: a torn restore leaves
orphaned bytes and no reachable root.

Buffers and extents persist across partitions *and* across upserts, resuming at
the next `DISK_PAGE_SIZE` boundary. Per-upsert padding over 256 shard upserts is
then ~2 MB total; a fresh extent per upsert would waste up to 8 MB × workers ×
256.

### What the baseline loses

Gone from the tree: `ParallelUpsertContext::PendingWrite`, `Partition::writes`,
`Partition::collect_writes`, `collect_partition_writes_`, `retire_partition_`,
and the in-memory-aux comment contract in `build_partition_subtrie`. The worker
runs the unmodified create recursion.

## Testing

Every case below is verified by injection, not by passing: the assertion that
proves the case is exercised must be shown to fire when the mechanism is disabled.

- `DbBinarySnapshot.ParallelMerklizationMatchesSerial` and
  `ParallelLoadMatchesSerialSlot` (both-on case) stay green. These read every
  account and slot back, which is what catches a bad `fnext`; a root hash cannot,
  since it is independent of child offsets.
- **Extent interleaving.** `parallel_upsert_test.cpp` gains an extent-size
  override small enough that every worker crosses several extents and their
  reservations interleave, at {1, 2, 8} workers, compared against the in-memory
  serial root plus full read-back.
- **Extent-boundary node placement.** An extent size just above a node's disk
  size, so a node lands at the last usable offset of one extent and its sibling
  at the first of the next.
- **Oversized node.** A leaf value exceeding the (overridden) extent size, taking
  the bespoke-reservation path.
- **Reservation guard.** The new `offset + size <= cursor` check exercised by the
  ordinary parallel tests; no death test, matching the existing choice not to add
  one for the snapshot kind-mismatch assert.
- **Compaction after a parallel restore.**
  `DbBinarySnapshot.CompactionAfterParallelRestore` (in place). It verifies every
  stored min-offset pair against offsets recomputed from the `fnext` arrays, then
  drives real slow-list compaction over the restored region and reads back. Note
  what it can and cannot catch: the per-pair verification is exact, but the
  compaction drive alone cannot detect a *uniformly* too-high minimum, because
  `advance_compact_offsets` derives the boundary from the same minimum it then
  checks against. Injecting a min that omits the children's minima passes the
  compaction drive and fails only the per-pair verification, so keep both.

## Risks and open verification items

1. **Compaction ordering — audited, no blocker.** Interleaved extents break
   global post-order monotonicity of virtual offsets. Every consumer of
   `min_offset_fast/slow` and of `compact_virtual_chunk_offset_t` was read; all
   of them fall into one of three order-independent shapes.

   *Takes a minimum.* `calc_min_offsets` (`trie.hpp:566-583`) is
   `std::min` over the children's stored pairs plus, optionally, the node's own
   offset — the result is a true minimum whichever side of its children the
   parent lands on. Every writer of the arrays goes through it or copies an
   existing entry verbatim: `create_node_from_children_if_any` (which is also the
   worker's path), `fillin_parent_after_expiration`
   (`trie.cpp:1323`), `try_fillin_parent_with_rewritten_node`
   (`trie.cpp:1472-1491`, which explicitly folds the *new* offset in with
   `std::min`, i.e. already tolerates it being lower than a child's),
   `mismatch_handler_` (`trie.cpp:1229`), `copy_trie.cpp:52,61,94,102,138,266`,
   `ChildData::copy_old_child` (`node.cpp:495`),
   `create_node_with_children` (`node.cpp:590-598`) and
   `create_node_with_expired_branches` (`trie.cpp:509-522`). Same shape at the
   GC boundary: `release_unreferenced_chunks` (`update_aux.cpp:612-650`) and
   `calculate_disk_usage_if_erased_up_to_and_including`
   (`update_aux.cpp:699-737`) take a component-wise min over the timelines'
   oldest roots and convert `get_count()` to a chunk count.

   *Compares against a compaction cutoff.* `maybe_expire_or_compact_child`
   (`trie.cpp:169,177`), the `compact_` child loop (`trie.cpp:1443-1453`), the
   fast-vs-slow placement decision (`trie.cpp:1414-1422`, node's own offset
   against the cutoff), the three corruption asserts (`trie.cpp:583-585`,
   `trie.cpp:1492`, `update_aux.cpp:905`) and
   `collect_compaction_read_stats` (`update_aux.cpp:1262`). All of these are
   subtrie-min against a per-timeline boundary; none relates a parent to a
   child.

   *Uses a virtual offset as an identity, not an order.* The read path only ever
   tests a virtual offset for equality (stale-recycle detection) or uses it as
   the `NodeCache` key: `find_notify_fiber.cpp:139-140,296-306,367-370`,
   `find_request_sender.hpp:183-190,250-258`, `db.cpp:1554-1556,1612-1614`,
   `node_cache.hpp`.

   Nothing outside `category/mpt` touches the arrays at all.

   Only four sites order virtual offsets, and none of them is parent-vs-child:

   - `trie.cpp:614-620` — the one the design flagged, `child offset < service
     writer's offset`. Confirmed to be on the single-child re-read branch of
     `create_node_compute_data_possibly_async`, which the pure-insert path
     (`create_new_trie_` → `create_node_from_children_if_any`) does not call at
     all. Measured, not assumed: with a `fprintf` in that branch, all seven
     `DbBinarySnapshot` tests — including a 256-shard parallel restore at 8
     workers — and `db_test`, `merkle_trie_test`, `monad_trie_test`,
     `compaction_test`, `update_aux_test`, `subtrie_version_test`,
     `min_truncated_offsets_test`, `virtual_offset_test`, `append_test`,
     `dual_timeline_test` reach it zero times. Reachability depends only on trie
     shape and the caching policy (a single-child node whose child was evicted),
     neither of which worker writes changes. The assert nevertheless becomes
     *semantically* wrong for the duration of a worker-writes upsert, because a
     worker extent legitimately sits ahead of the service writer: Task 3 should
     re-base it on the reservation cursor rather than
     `node_writer_fast/slow->sender().offset()`, or drop it.
   - `rewind_to_match_offsets` (`update_aux.cpp:164-165,179-180`) — last root
     vs. the metadata's `start_of_wip` offset. Holds as long as
     `advance_db_offsets_to` is given the reservation cursor rather than the
     service writer's offset (§Chunk grants); risk item 3 is the same question.
   - `rewind_to_version` (`update_aux.cpp:339-340`) — max of two timelines'
     post-root offsets.
   - the disk-growth arithmetic (`update_aux.cpp:852-861,939-974`) samples
     `node_writer_fast->sender().offset()` and subtracts a previous mark, so it
     assumes the *service writer's* offset increases monotonically, which it
     does. It would understate growth if worker writes and compaction ever ran
     together, but `db.cpp:462` asserts they cannot.

   **Verdict: no consumer assumes a parent's virtual offset exceeds its
   children's.** That is the whole of what this audit establishes: losing
   post-order monotonicity is not by itself a hazard. It is *not* a claim that
   the min-offset machinery is safe under worker writes in general — see the
   precondition below, which is a separate hazard the same audit turned up.

   Pinned by `DbBinarySnapshot.CompactionAfterParallelRestore`, which restores in
   parallel, verifies every stored min-offset pair in the restored trie against
   offsets recomputed from the `fnext` arrays, then drives eight versions of real
   slow-list compaction across the restored region and reads every account and
   slot back.
2. **Precondition: a chunk must be on the fast or slow list before any worker
   writes into it.** `physical_to_virtual` (`update_aux.cpp:76-91`) returns
   `INVALID_VIRTUAL_OFFSET` for an offset whose chunk is still on the free list,
   and `calc_min_offsets` (`trie.hpp:571-574`) then silently *skips* folding the
   node's own offset into the pair. The result is a uniformly too-high minimum —
   exactly the corruption class the compaction drive in the test cannot detect
   (§Testing) — and the failure surfaces much later, as either the
   `update_aux.cpp:906` abort or `free_compacted_chunks` releasing a chunk that
   still holds live nodes.

   So chunk grant is ordered **append-to-list before extent hand-out**, not
   reserve-then-append; both grant sites carry a comment saying why. Every feed of
   `physical_to_virtual` into `calc_min_offsets` on the write path guards this with
   `MONAD_ASSERT(virtual_offset != INVALID_VIRTUAL_OFFSET)` —
   `create_node_from_children_if_any` and `fillin_parent_after_expiration`
   (`trie.cpp:1322`). The worker needs no assert of its own: it reaches the arrays
   only through that same recursion, which is what turns a mis-ordered grant into
   an abort instead of silent corruption. Two things do
   *not* catch it: `trie.cpp:1325-1327` is an `||`, so it passes when only one
   component is invalid, and `copy_trie.cpp:52-53,138-139` feed
   `physical_to_virtual` straight into `calc_min_offsets` with no check at all.
3. **Cursor versus metadata offset at open — resolved, they cannot disagree.**
   `rewind_to_match_offsets` trims both work-in-progress chunks to the recorded
   fast/slow offsets (`update_aux.cpp:217,229`) before `reset_node_writers` runs,
   and `try_trim_contents` stores `min(chunk_bytes_used, bytes)`, so a cursor a
   crash left ahead is reconciled *downward* to the record. The metadata offset
   is therefore authoritative at open and the reservation cursor is authoritative
   during a run. `reset_node_writers` nevertheless positions each writer at what
   `reserve()` returns and logs the gap when the cursor is ahead, which orphans
   those bytes rather than overwriting them; across the whole `monad_trie`,
   `monad_async` and `DbBinarySnapshot` suites the gap was never non-zero.
4. **Zoned devices.** Out-of-order intra-chunk writes are incompatible with
   sequential-write-required zones. Unimplemented today; recorded so the
   constraint is not rediscovered later.

## Measured

Same harness and oracle as the combined measurement: mainnet block 90045827
(11 GB, 256 shards), slot/`ethereum` target, warm cache, per-thread CPU sampler,
and the restored root read back and compared against the snapshot header's own
`state_root`. Every row below produced
`0x4aa9630da0d07bff562084bf09e58c5256198082fb93ba04d1c2c134f6d3fe11`.

| `--load-concurrency` | `--upsert-concurrency` | wall | vs serial | peak RSS |
|---|---|---|---|---|
| 1 | 0 | 215.4 s | 1.00× | 6.50 GB |
| auto (16) | 0 | 165.7 s | 1.30× | 13.87 GB |
| auto (16) | 16 — before | 80.1 s | 2.66× | 16.69 GB |
| auto (16) | 16 — after | **~31 s** | **~6.9×** | 13.92 GB |

The after row is two runs, 31.7 s and 30.9 s — a 2.6% spread, which is why it is
quoted to two significant figures and not as a mean. Serial reproduces the earlier
round's 212.9 s to 1.2% and Phase-1-only its 162.3 s to 2.1%; that is the noise
this comparison carries.

Nothing short-circuited: `getrusage` file-system output is 72,238,208 blocks of
512 B against serial's 72,237,904 — **0.0004% apart** — so all three configurations
wrote the same 37 GB, and the root hash says they wrote it correctly.

**The prediction held on the mechanism and badly understated the result.** The
service thread's write path and allocator went from 13.9 s and 7.9 s (shares from
the merklization-only profile, §Goal) to 0.36 s and 0.32 s — ~21 s removed against
an estimate of ~20 s. But the wall did not land at the predicted 60-65 s, it landed
at ~31 s.

The reason is not "superadditivity", which names a result rather than a mechanism.
The wall is very nearly the service thread's own CPU divided by its duty cycle:
50.6 / 0.63 = 80.3 s before, 21.6 / 0.68 = 31.7 s after, both within 0.3% of the
measured walls. That is close to an identity — duty *is* CPU over wall — so it
explains nothing by itself, but it localizes the wall to one thread and shows what
the estimate got wrong: it assumed duty would hold while CPU fell. Duty instead
*rose* 63 → 68%, so the wall fell by more than the CPU did. The two mechanisms
behind that are `Db::upsert` blocking its caller on a promise, which converts
service-thread time directly into loader idle time, and the fact that the service
thread's poll cost is partly a function of how long the run lasts, so a shorter
wall is self-reinforcing.

The service thread lost **29.0 s** in total (50.6 → 21.6), of which the write path
and allocator account for ~21 s. The remaining ~8 s is mostly io_uring polling,
measured at 14.9 → 7.6 s across the two profiles — a term the design never
predicted because it is a consequence of the wall shrinking rather than of moving
any work.

Two secondary predictions:

- **Peak RSS fell, 16.69 → 13.92 GB**, and is now within noise of Phase 1 on its
  own (13.87 GB). Merklization concurrency has stopped costing resident memory at
  all: what remains is Phase 1 holding in-flight shards. Against a *serial*
  restore, though, RSS still more than doubles (6.50 → 13.92 GB) and essentially
  all of that is Phase 1 — which is what
  `parallel_snapshot_restore_memory_bounding.md` exists to address.
- **Total CPU fell against the write-list baseline**, ~359 → ~277 s — against a
  *serial* restore it rises, 228 → 274 core-seconds, as the non-goal above
  states. The dominant cause of the fall is not allocator
  locality but that **the second StateMachine walk is gone**: a worker used to walk
  its finished subtrie again to build the write list, and per worker
  `collect_partition_writes_` (0.63 s) has disappeared while `MachineBase::down`
  fell 4.10 → 2.00 s. Over 16 workers that is the right order to be most of the
  drop. Allocator locality is the smaller term — service `malloc`/`free` 7.9 →
  0.32 s and per-worker 0.66 → 0.31 s, so roughly a quarter of it. Kernel mutex
  contention also collapsed on the workers, `osq_lock` 0.49 → 0.002 s each. Work
  was *eliminated*, not merely relocated, which is why a non-goal was over-achieved.

  The walk figure is the robust one: `MachineBase::down` per worker is 4.10 s before
  and **2.00 s in both** post-change records — 19.74% × 10.13 s user-only and 17.80%
  × 11.24 s kernel-inclusive — with `collect_partition_writes_` absent from both. So
  the halving survives both the precision setting and run-to-run noise.

  Three caveats. The before side is the merklization-only profile, so these are
  per-thread comparisons across two configurations, and the total-CPU drop itself
  cannot be decomposed exactly. The before record was taken at `precise_ip=0` and
  both after records at `precise_ip=2`, a boundary every per-symbol comparison here
  crosses; it redistributes samples *within* a tight loop's symbol family without
  moving the family's total much, which is why the figures quoted above are either
  whole buckets or symbols confirmed in both after records.

  And keccak is **not** usable as a control, for two independent reasons. Its
  per-invocation cost genuinely changes with concurrency: prep-side hashing, which is
  byte-for-byte identical and untouched by this branch, went **36.1 s on one loader
  thread to 45.7 s across 16 prep threads, +27%**, while effective clock fell
  4.95 → 4.63 GHz (cycles ÷ CPU-seconds) as concurrency rose 2.62 → 8.69 cores.
  Separately, per-thread keccak is not stable enough to compare: the two after
  records of the *same* configuration put worker keccak at 3.12 s and 3.90 s, a 25%
  spread, so against one of them keccak *fell* versus the before record's 3.21 s.
  Attribution inside the family swings likewise (`SHA3_absorb` 2.97 / 3.66 / 0.77%).
  The invocation count, by contrast, is pinned exactly — the matching root fixes the
  merklization-side node set and the snapshot fixes the prep side — so equal work is
  established by that and by the file-system output, never by equal hashing time.

### What the service thread does now

21.6 s of CPU across a 31.7 s wall — 68% duty, up from 63%, and still the busiest
single thread. Of that 21.6 s, **16.3 s is user and 5.3 s is system**, which matters
for reading any profile of it: a `--all-user` record sees only the 16.3 s, so
scaling its relative shares by 21.6 s inflates every bucket by a third and smears
the kernel time invisibly across user categories. The table below therefore comes
from a separate kernel-inclusive record of the same configuration
(`t6_both_kern.data`, 33.3 s wall, service thread 22.5 s of CPU), so shares and
scale share one run:

| bucket | share | seconds |
|---|---|---|
| merklization | 29.5% | 6.64 s |
| io_uring (user) | 20.6% | 4.62 s |
| keccak | 17.3% | 3.89 s |
| kernel: block I/O + page cache | 13.4% | 3.02 s |
| kernel: not separable from the above | 12.2% | 2.74 s |
| memcpy/memset | 1.9% | 0.42 s |
| write path | 1.6% | 0.36 s |
| malloc/free | 1.4% | 0.32 s |
| dispatch + locks | 0.9% | 0.20 s |

Grouped, the thread is **trie build 10.5 s (47%) against I/O 9.6 s (43%)**. The
bucket table's own split understates I/O, because the categories above are drawn by
symbol-name patterns that miss cases: of the 12.2% "not separable",

- **3.1 pp is I/O by symbol name** that the I/O pattern missed only because it
  requires `bio_`/`dm_` *with* a trailing underscore — `__split_and_process_bio`,
  `__map_bio`, `clone_endio`, `linear_map`, `alloc_io`, `alloc_tio`,
  `ll_back_merge_fn`, `end_buffer_async_write`, `try_to_free_buffers`,
  `block_commit_write`, `mempool_*`;
- **5.8 pp is slab, memcg and page-allocator churn** — `kernel_init_pages` alone is
  2.4 pp, plus `__memcg_slab_free_hook`, `kmem_cache_free`, `refill_obj_stock` —
  which exists to allocate the `bio` and `buffer_head` objects the I/O path consumes;
- only **3.3 pp is generic** (scheduler, RCU, page faults, speculation thunks).

So I/O is **at least 8.3 s (37%)** counting only what is named for I/O, **9.6 s
(43%)** once the allocator churn serving it is included, and **10.4 s (46%)** if all
kernel time is charged to it.

The decisive argument does not depend on that split. The 16 merklization workers run
the *same trie-build code* and spend **0.14-0.17 s of system time against ~10.6 s of
user — 1.3-1.6%** — while this thread is 5.30 s of 21.63 s, **24.5%**. Whatever the
service thread's kernel time is, it is not trie build. **So trie build and I/O are
co-equal on this thread**; I/O is not a minor residue, and the earlier reading of it
as "28%" was an artifact of the user-only scaling described above.

The trie-build half is not residue from the unpartitioned top levels. Every
trie-build symbol sits at a *proportional* share of its value on a worker —
~0.6-0.75 across symbols, and as low as 0.55 against the busiest worker
(`__KeccakF1600` 17.33 vs 25.77%, `MachineBase::down` 13.14 vs 19.74%,
`decode_storage_db_raw` 1.60 vs 2.57%, `encode_16_children` 0.35 vs 0.51%) — which
is what helping through `wait()` looks like: the same work, scaled. Top-level-only
work would be the opposite shape, with `encode_16_children` over-represented and a
storage-leaf decode near zero. So driving the trie-build half down moves it to a
worker rather than deleting it, which is why the next lever is elsewhere (see
`parallel_merklization_design.md`, "Remaining headroom"). Those ratios are from the
user-only record, where they are internally consistent because both sides are
scaled the same way.

## Rollout

Worker writes are inert unless `--upsert-concurrency` is set, so the default
restore path and all of block execution keep today's behavior.

One limitation comes with the flag: because the workers take extents from one
chunk list, and which list that is follows from the first upsert's
`can_write_to_fast`, a db opened with `--upsert-concurrency` is bound to one
destination for its whole life. A snapshot restore writes to the slow list, so
the same `Db` cannot afterwards serve ordinary block upserts, which write to the
fast one; `init_parallel_extents` aborts with that message rather than mixing the
two. The snapshot loader opens its own `Db` and closes it, so nothing in the
product hits this. The reservation
refactor is shared code and ships with it; it is behavior-preserving for the
single-writer case.

The `#2463`/`#2464` snapshot-format chain conflicts with parallel prep in
`db_snapshot.cpp` (prep removes `bytes_read`/`BYTES_READ_BEFORE_FLUSH` outright,
the chain lowers that threshold and adds group-boundary flushes). This design does
not touch `db_snapshot.cpp` and so adds nothing to that conflict.
