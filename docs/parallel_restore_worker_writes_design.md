# Worker-side node writes for parallel restore — design

> Each merklization worker gets a reserved byte range in the fast chunk and an
> 8 MB buffer, runs the ordinary write-and-evict recursion against it, and
> `pwrite`s the buffer itself. Node serialization, disk-offset assignment and
> node freeing leave the triedb service thread. Enabled only for the snapshot
> restore path.
>
> `file:line` references are against `34c374ec6`; if they drift, grep the cited
> symbol.

## Goal / non-goals

**Goal.** Take the write path and the allocator off the triedb service thread,
which the combined parallel-restore profile identifies as the remaining ceiling.
In the 80.1 s combined run the service thread is busy 50.6 s (63% duty) and is
the dominant single thread; of that, the write path (offset allocation,
`fnext`/`min_offset` patching, serialization) is ~28% ≈ 14 s and `malloc`/`free`
is ~15% ≈ 7.6 s. Both are per-node costs that belong wherever the node was
built.

**Non-goals.**

- **Not** enabling worker writes for block execution. They exist only behind
  `--upsert-concurrency`, which only the snapshot loader sets.
- **Not** an arena that doubles as the write buffer. Nodes stay
  `malloc`-allocated; only *where* they are serialized and freed changes. In-place
  construction founders on `Node`'s memory-only `next` SharedPtr tail
  (`node.hpp:169-186`), which is inside the allocation but outside the disk image,
  and on `allocate_shared`'s inline control block: neither leaves room for the
  4-byte size prefix at the alignment the format needs.
- **Not** reducing total CPU. Malloc and the serialize memcpy still happen; they
  move to threads that are idle. Peak measured demand for the whole combined job
  was 6.9 of 16 cores.
- **Not** changing the snapshot format, the wire, or the dump side.

**Scope caveat.** The reservation change below is *not* restore-only. The service
thread's own writer submits through `AsyncIO::submit_request_`, so reserve-at-grant
is a shared-path change. It leaves live-execution behavior identical — same
offsets, same write order — and replaces a guard that cannot detect misplacement
with one that can.

## Background

Today a worker builds its partition against an in-memory `UpdateAux`, which
suppresses writes because `create_node_from_children_if_any` gates its
write-and-evict loop on `aux.is_on_disk()` (`trie.cpp:569`). The whole subtrie
therefore stays resident, the worker records a post-order write list
(`collect_partition_writes_`, `trie.cpp:731`), and the service thread replays it
flat in `retire_partition_` (`trie.cpp:760`):

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

That loop is the whole cost. The last line drops the only owning reference to a
node the worker allocated, so every eviction is a cross-thread cold free — the
23× `unlink_chunk` in the profile is that signature. The rest is the write path
itself.

The serial recursion already does exactly the same four things on the thread that
built the node (`trie.cpp:569-593`). So the change is not to add a mechanism but
to stop suppressing the one that exists.

### Why offsets can be assigned locally

`collect_partition_writes_` is post-order because a parent's `fnext` array is part
of its own disk image, so children must have offsets first. The create recursion
is already post-order for the same reason. Given a private byte range, a worker
can satisfy that ordering without consulting anybody: `physical_to_virtual`
(`update_aux.cpp:74-91`) reads only `atomic_load_chunk_info(..., acquire)` and an
`insertion_count` that is fixed once the chunk is on the fast list, so
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
- Writer creation reserves. `reset_node_writers` (`update_aux.cpp:474-486`),
  `replace_node_writer` and `replace_node_writer_to_start_at_new_chunk`
  (`trie.cpp:1561,1637`) each already compute `bytes_to_write`; the writer's
  offset becomes the reserved offset rather than
  `offset + written_buffer_bytes()`.
- `submit_request_` writes at the caller's offset and asserts
  `offset + size <= reservation cursor`, which is a check on placement rather
  than on the low bits of an address.

Out-of-order writes within a chunk are then fine on files and block devices. They
are not fine on genuinely zoned devices — but `write_fd` `MONAD_ABORT`s on zonefs
today (`storage_pool.cpp:181`), so this is a trade we are stating, not a contract
we are breaking silently.

### The worker writer

`WorkerNodeWriter`, one per worker **thread** — not per partition — in
`parallel_upsert.{hpp,cpp}`:

- Owns an `aligned_alloc(DMA_PAGE_SIZE, WORKER_EXTENT_BYTES)` buffer for its
  lifetime. No registered-buffer pool, so `wr_buffers` stays at its default of 4
  (`ondisk_db_config.hpp:37`).
- Holds a reserved range `[base, base + len)` in the current fast chunk and a
  cursor. `append(Node const &)` serializes with `serialize_node_to_buffer` and
  returns the `chunk_offset_t`, with the `spare` page count set exactly as
  `async_write_node_set_spare` does (`trie.cpp:1826-1827`).
- When the node does not fit: pad the tail to `DISK_PAGE_SIZE` with `memset`,
  `pwrite` the buffer at `write_offset(base + flushed)`, and reserve the next
  extent. Blocking is deliberate — ~4 ms per 8 MB on NVMe, on a thread that is
  otherwise hashing.
- `WORKER_EXTENT_BYTES == AsyncIO::WRITE_BUFFER_SIZE`. No CLI knob, but a
  test-only override on `ParallelUpsertContext`, for the same reason
  `set_flush_bytes` has one and no flag: at unit-test scale a production-sized
  extent means the boundary paths never execute.

A node larger than an extent gets its own reservation of
`round_up_align<DISK_PAGE_BITS>(disk_size)` and is written directly from the node
rather than through the buffer. Restore values top out far below 8 MB, but
`Node::max_disk_size` is 256 MB and an abort in that corner is not acceptable.

### Chunk grants

Extents inside a chunk are lock-free: one atomic cursor, reservation order
defines placement. Crossing a chunk needs a free-list pop and a
`metadata_ctx().append`, which stay service-thread-only. A worker whose
reservation would exceed `chunk_capacity` clamps to the 512-aligned remainder and
requests the next chunk through the context. At 256 MB per chunk that is ~44
grants for an 11 GB restore.

`advance_db_offsets_to` (`trie.cpp:1870`) then takes the reservation cursor rather
than the service writer's offset, since worker extents may sit ahead of it. Gaps
below the cursor — a worker's partly-used extent — are orphaned bytes; nothing
scans the region, every node is reached by a recorded offset.

### Which writer a partition uses

`wait()` helps rather than idles, so a partition can run on any pool thread *or on
the service thread itself*. Writer selection is therefore by thread, not by
partition: a pool thread serializes into its own `WorkerNodeWriter`, and the
service thread keeps using `node_writer_fast` and the uring path exactly as
today. Nested partitions inherit the same rule, so a subtrie can span two
writers — which is sound, because a child's offset is final before its parent is
serialized regardless of which extent it landed in.

### What the worker aux may touch

The worker's `UpdateAux` is constructed per partition as it is now, plus
`set_parallel(&ctx)` so nested partitioning still fires. It must report
`is_on_disk()`, which is `io != nullptr` (`trie.hpp:374`), so it carries the
service thread's `AsyncIO` pointer — but only for `chunk_capacity`, `chunk_count`
and `storage_pool().chunk()`. Writes dispatch to the calling thread's writer at
the single site `async_write_node_set_spare`, so a pool thread never enters
`async_write_node`, whose first statement is
`aux.io->poll_nonblocking_if_not_within_completions(1)` (`trie.cpp:1690`).

To make that a checked property rather than a convention, `AsyncIO` records its
owning thread at construction and `MONAD_DEBUG_ASSERT`s ownership in `poll_*`
and `make_connected`. Debug-only: `poll_*` is hot in live execution.

`metadata_ctx` is read concurrently and only through
`atomic_load_chunk_info`. Nothing on the worker mutates it.

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

### What gets deleted

`ParallelUpsertContext::PendingWrite`, `Partition::writes`,
`Partition::collect_writes`, `collect_partition_writes_` (`trie.cpp:731-755`),
`retire_partition_` (`trie.cpp:760-774`), and the in-memory-aux comment contract
in `build_partition_subtrie`. The worker runs the unmodified create recursion.

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
   existing entry verbatim: `create_node_from_children_if_any` (`trie.cpp:581`),
   `retire_partition_` (`trie.cpp:767`), `fillin_parent_after_expiration`
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

   So chunk grant must be ordered **append-to-list before extent hand-out**, not
   reserve-then-append. Every existing feed of `physical_to_virtual` into
   `calc_min_offsets` on the write path guards this with
   `MONAD_ASSERT(virtual_offset != INVALID_VIRTUAL_OFFSET)` —
   `create_node_from_children_if_any` (`trie.cpp:580`), `retire_partition_`
   (`trie.cpp:765`), `fillin_parent_after_expiration` (`trie.cpp:1322`) — and
   `WorkerNodeWriter` must carry the same assert, since it is what turns a
   mis-ordered grant into an abort instead of silent corruption. Two things do
   *not* catch it: `trie.cpp:1325-1327` is an `||`, so it passes when only one
   component is invalid, and `copy_trie.cpp:52-53,138-139` feed
   `physical_to_virtual` straight into `calc_min_offsets` with no check at all.
3. **Cursor versus metadata offset at open.** If a crash can leave
   `chunk_bytes_used` ahead of the metadata's recorded fast/slow offsets, then
   reserve-at-grant resumes at the cursor and leaves a gap, where today's writer
   resumes at the metadata offset. Confirm which is authoritative on open and
   state the reconciliation rule.
4. **Zoned devices.** Out-of-order intra-chunk writes are incompatible with
   sequential-write-required zones. Unimplemented today; recorded so the
   constraint is not rediscovered later.

## Measurement plan

Same harness and oracle as the combined measurement: mainnet block 90045827
(11 GB, 256 shards), slot/`ethereum` target, warm cache, `combo_profile.sh <load>
<upsert> <tag>` plus the per-thread CPU sampler, and the restored root read back
and compared against the snapshot header's own `state_root`
(`0x4aa9630d…`). Configs: serial, Phase 1 only, both-on before, both-on after.

Expected: the service thread loses ~20 s of the ~50.6 s it burns in the 80.1 s
combined run, taking the wall to roughly 60-65 s — **~3.3-3.5× cumulative** — with
peak RSS *falling*, since 16 × 8 MB of buffers replaces multi-GB of resident
subtries. What remains on the service thread afterwards is the unpartitioned
merklization of the top levels (~12.8% ≈ 6.5 s) and io_uring.

## Rollout

Worker writes are inert unless `--upsert-concurrency` is set, so the default
restore path and all of block execution keep today's behavior. The reservation
refactor is shared code and ships with it; it is behavior-preserving for the
single-writer case.

The `#2463`/`#2464` snapshot-format chain conflicts with parallel prep in
`db_snapshot.cpp` (prep removes `bytes_read`/`BYTES_READ_BEFORE_FLUSH` outright,
the chain lowers that threshold and adds group-boundary flushes). This design does
not touch `db_snapshot.cpp` and so adds nothing to that conflict.
