# Dual-timeline metadata

## Purpose

During a chain fork, execution must serve both the pre-fork canonical
chain and the forked branch from the same on-disk state. The dual-
timeline design gives `UpdateAux` two physical root-offset rings and
three lifecycle primitives — `activate_secondary`, `promote`, and
`deactivate_secondary` — to orchestrate the transition without taking
the DB offline and without duplicating the full node-index.

This document covers the metadata layer only: how the two rings live
inside the existing `db_metadata`, how promote flips the "which ring
is primary" label atomically, how shrink/grow redistributes cnv
chunks between the rings while preserving crash safety, and how the
constructor recovers from a crash that lands mid-operation.

## Layout

The two rings, `ring_a` and `ring_b`, share one header type
(`root_offsets_ring_t`) and each has its own cnv-chunks-backed
storage. Both live inside `db_metadata`:

```
db_metadata {
    // existing fields (magic, chunk counts, db_offsets, consensus
    // versions) ...
    root_offsets_ring_t root_offsets;        // ring_a
    root_offsets_ring_t secondary_timeline;  // ring_b
    uint8_t primary_ring_idx;                // 0 = ring_a, 1 = ring_b
    uint8_t secondary_timeline_active_;      // 1 if non-primary ring is live
    uint64_t shrink_grow_seq_;               // seqlock (see below)
    pending_shrink_grow_t pending_shrink_grow;  // intent log (see below)
    uint8_t future_variables_unused[...];
    // chunk lists ...
}
```

The fixed header is still 4480 bytes; new fields were carved out of
`future_variables_unused`, which `init_new_pool` zero-fills (matching
the MONAD007→008 migration), so pre-existing MONAD008 pools see the
new fields as their idle state on first reopen.

`root_offsets_ring_t::SIZE_` dropped 65536 → 32. The original
cnv_chunks[] array was vastly over-provisioned for the real chunk
counts used by the pool.

## Physical vs logical ring

At pool init, `primary_ring_idx = 0` and all cnv ring chunks go to
`ring_a`. `ring_b` starts with `cnv_chunks_len = 0`. The "primary"
role is a label: which physical ring a query routes to depends on
`primary_ring_idx`, not on the struct field name.

`promote_secondary_to_primary_header` is therefore a single atomic
byte flip of `primary_ring_idx` on both metadata copies. Header
fields don't move and in-memory spans don't swap — the role change
is observed at query time via `root_offsets(timeline_id)`.

Both copies hold their `is_dirty` bit across both flips
simultaneously. If a crash lands between the two flips, dirty-bit
recovery on reopen propagates the clean copy over the dirty one,
yielding either "both flipped" or "neither flipped" — never "the two
copies disagree on which ring is primary." Since the physical ring
carrying the role keeps its own header and data across a promote,
the DB remains consistent either way.

## Shrink/grow (activate/deactivate)

`activate_secondary_header(fork_version)` atomically shrinks the
primary ring by half and hands the freed cnv chunks to the other
ring, which becomes the secondary role's backing store initialised at
`fork_version`. `deactivate_secondary_header` reverses the transfer.

Both require the primary's cnv_chunks_len to be a power of two;
ring-position computation uses `v & (cap − 1)`.

### VA stability

The ring span pointers (`ring_a_span`, `ring_b_span`) are stable
across shrink/grow. Each ring reserves its max-size virtual address
range at startup; `MAP_FIXED` installs individual cnv chunks into
their slots on activate/deactivate. A slot outside the currently-
occupied prefix remains `PROT_NONE` anonymous.

### The crash-corruption window

Ring data (primary/secondary spans) and the metadata page live in
*different* backing files from the kernel pagecache's perspective:
the metadata is mmap'd on cnv chunk 0, and each ring slot is mmap'd
on a cnv chunk 1..N. Kernel writeback of these pages is independent
and unordered.

A naïve shrink would touch the ring pages (in-place copy of entries
from the discarded half into the retained half) and then update
`cnv_chunks_len` on the metadata page. If the kernel flushes the
ring pages before the metadata page and a crash occurs in that
window, on reopen the metadata still shows the old capacity but the
ring has overwritten low-index slots. Readers index under the old
capacity mask, land on slots that now carry data for different
versions, and get silently wrong answers.

The existing dual-copy + `is_dirty` recovery can't detect this:
`is_dirty` lives in the metadata page that wasn't flushed, so
recovery sees both copies clean. And `db_copy` only propagates
metadata — it doesn't touch ring data.

### The intent-log protocol

`pending_shrink_grow` is a stamp on the metadata page that records
the in-flight operation:

```
struct pending_shrink_grow_t {
    uint32_t op_kind;                  // NONE | ACTIVATE | DEACTIVATE
    uint32_t target_primary_chunks;    // post-op primary cnv_chunks_len
    uint64_t fork_version;             // meaningful for ACTIVATE
}
```

The public API wraps each operation in six steps:

```
1. set_pending_shrink_grow_ (stamp flag, bump seq to odd) under
   hold_dirty, per copy
2. sync_metadata_to_disk_   (msync + fsync cnv chunk 0)
3. do_*_secondary_body_     (idempotent ring copy + commit)
4. sync_ring_data_to_disk_  (msync ring pages + fsync each backing
                              cnv chunk)
5. sync_metadata_to_disk_
6. clear_pending_shrink_grow_ (unstamp flag, bump seq to even) under
   hold_dirty, per copy
7. sync_metadata_to_disk_
```

On any crash, the constructor's `replay_pending_shrink_grow_` fires
if either copy has `op_kind != NONE` (see Recovery below) and runs
the body to completion.

### Body idempotency

Every step in `do_activate_secondary_body_` and
`do_deactivate_secondary_body_` is safe to re-run against any partial
state the body itself could have produced:

- **`version_lower_bound_` bump.** `std::max(cur_lb, ...)` is a fixed
  point under repeated application.
- **Ring-copy loop.** Sources are in `[new_cap, old_cap)` (for
  activate; symmetric for deactivate); destinations are in
  `[0, new_cap)`. Ranges are disjoint, and the loop never writes to
  a source slot. Re-running the loop with the same source contents
  produces the same destination state.
- **`MAP_FIXED` installs.** Happen *before* the `cnv_chunks[]` swap.
  If an install fails, the cnv_chunks state is still whole, so
  recovery remains unambiguous. Each install is idempotent (it
  replaces any existing mapping) and the source chunk id is derived
  from either `sstore.cnv_chunks[k]` (already moved in a prior
  partial run) or `pstore.cnv_chunks[new_chunks + k]` (not yet
  moved).
- **`cnv_chunks[]` move.** Guarded on the destination slot's current
  id: if `sstore.cnv_chunks[k].cnv_chunk_id != uint32_t(-1)`, the
  move has already run for this k — skip.
- **Secondary ring init (memset + version fields).** Safe to re-run
  because replay executes in the constructor before any client
  thread can observe the DB, and the live-path public API is
  synchronous — no push can have touched the post-activate state
  until the API call returns (after the flag-clear msync).
- **`cnv_chunks_len` commit and `secondary_timeline_active_` flip.**
  Plain stores of the target value; re-running sets the same value.

`map_ring_a_storage` / `map_ring_b_storage` tolerate
`cnv_chunks[k].cnv_chunk_id == uint32_t(-1)` so a crash mid-swap
doesn't prevent the constructor from reaching the replay path.

## Concurrent readers

Readers use a seqlock, `shrink_grow_seq_`, to retry if a shrink/grow
commits or replay runs while they're reading:

```
do {
    seq = shrink_grow_seq_acquire();  // copy 0
    if (seq & 1u) { yield; continue; }
    ... read ring snapshot ...
} while (seq != shrink_grow_seq_acquire());
```

The seq is bumped under the same `hold_dirty` as the intent-log
stamp/clear, so a durable odd seq is always accompanied by a non-
`NONE` op_kind — replay on reopen always restores even parity before
any reader observes the DB.

### Parity alignment after partial-stamp crash

The set/clear scopes run per copy with the `hold_dirty` scope closed
between them. If a crash lands between the two scopes — copy 0
stamped and clean, copy 1 unstamped and clean — neither is dirty and
the dirty-bit path does nothing. Replay fires because copy 0 has
`op_kind != NONE`, runs the body, then calls `clear_pending_shrink_
grow_`.

A blind `fetch_add(1)` on each copy's seq in the clear path would
leave copy 0 even but copy 1 odd. If copy 0 were later healed from
copy 1 via `db_copy`, readers of copy 0 would spin on the seqlock.

Instead, clear stores `(cur + 2) & ~1ULL` — the smallest even value
strictly greater than `cur`. Set stores `(cur + 1) | 1ULL` — the
smallest odd value strictly greater than `cur`. Both copies end at
the correct parity regardless of their starting state, and each
copy's generation counter strictly advances.

## Constructor recovery

The constructor runs, in order:

1. Magic validation (restore corrupted copy 0 from copy 1 via
   `db_copy` if needed).
2. MONAD007 → MONAD008 migration (see section below).
3. Version-mismatch check.
4. Dirty-bit recovery (`is_dirty` on one copy → `db_copy` from the
   other).
5. `map_ring_a_storage` / `map_ring_b_storage` (tolerant of
   `uint32_t(-1)` cnv_chunk_ids from a partial swap).
6. `replay_pending_shrink_grow_`:
   - If both copies have non-NONE `op_kind`, assert byte-wise
     equality of the pending records (defends against protocol
     regression / out-of-band corruption).
   - Use whichever copy has `op_kind != NONE` (single-side case
     arises when the crash fell in the gap between set/clear scopes).
   - Run the appropriate `do_*_body_` with the stamped params.
   - `sync_ring_data_to_disk_`, `sync_metadata_to_disk_`.
   - `clear_pending_shrink_grow_`, `sync_metadata_to_disk_`.

Readers only observe the DB after the constructor returns, so the
replay runs without concurrency.

## MONAD007 → MONAD008 layout-shift migration

MONAD008 dropped `root_offsets_ring_t::SIZE_` from 65536 to 32, which
took `sizeof(db_metadata)` from 528512 bytes to 4480. The flexible
`chunk_info[]` array therefore moved from file offset 528512 to 4480,
and several fields that lived at the end of the old header moved too:

| Field                                          | MONAD007 offset | MONAD008 offset |
|------------------------------------------------|-----------------|-----------------|
| `db_offsets` + consensus block (128 bytes)     | 524328          | 296             |
| free/fast/slow list triple (24 bytes)          | 528488          | 4456            |
| `chunk_info[]` (flexible)                      | 528512          | 4480            |

The first 24 bytes (magic, `chunk_info_count` bitfield,
`capacity_in_free_list`) sit at the same offsets in both layouts, and
so do `root_offsets.version_lower_bound_` / `next_version_` / the
`storage_` header. The first 31 `cnv_chunks[]` entries (the max a
MONAD008 pool can hold) also survive in place; MONAD007 pools that
somehow populated `cnv_chunks[31..65534]` cannot be migrated and the
ctor aborts.

**mmap sizing.** To read from offset 528512+ on a MONAD007 pool, the
ctor maps the full half-capacity of cnv chunk 0 (we guarantee metadata
never spans multiple chunks, so the half-chunk always covers any past
or future fixed-header layout). `db_map_size_` tracks the small
logical metadata region — used for `msync`, `db_copy`, and similar
ops — while `metadata_mmap_size_` tracks the VA reservation used for
mmap/munmap.

**Migration steps** (per copy, under `hold_dirty`):

1. Assert `root_offsets.storage_.cnv_chunks_len < SIZE_` — the live
   chunks list must fit under MONAD008's cap.
2. `memmove` `chunk_info[]` from file offset 528512 to 4480
   (`chunk_count × sizeof(chunk_info_t)` bytes; ranges are disjoint
   for any realistic `chunk_count`).
3. `memcpy` the list triple from offset 528488 to 4456.
4. `memcpy` the `db_offsets` + consensus block (128 bytes) from 524328
   to 296.
5. Zero the region `[&secondary_timeline, &free_list)` so every
   new-in-MONAD008 field starts at its idle value (secondary inactive,
   `shrink_grow_seq_` even, `pending_shrink_grow.op_kind == NONE`).
   Without this, MONAD007's `0xff` padding would make the secondary
   look active, stick the seqlock at odd, and set `op_kind` to an
   unknown value that replay would reject.
6. Bump the magic to MONAD008.

After both copies finish, `sync_metadata_to_disk_` commits the
relocated layout before downstream ctor code reads through the new
offsets.

**Crash safety.** Each copy is migrated under `hold_dirty`, so a
crash mid-copy leaves `is_dirty = 1` and the magic-validation heal on
the next open copies the already-migrated sibling over the stragglier
(the heal's `db_copy` is layout-agnostic since the on-disk MONAD008
bytes form a valid image). Crashes between copies are covered by the
per-copy loop restarting on MONAD007-magic copies. The individual
`memmove`/`memcpy`/`memset` operations don't overwrite their sources,
so even a fully-restarted migration on a mid-migrated pool is
idempotent.

## CLI restore

`do_restore_database` in `cli_tool_impl.cpp` copies these fields from
the archive's `db_metadata`:

- `root_offsets` (header + storage)
- `secondary_timeline` (header + storage)
- `primary_ring_idx`, `secondary_timeline_active_`
- consensus versions and block IDs

Explicitly **not** copied (left at init zero):

- `shrink_grow_seq_`
- `pending_shrink_grow`

Starting the restored DB from a quiescent state avoids replaying an
archive-era in-flight op against freshly-restored ring data whose
layout assumptions may differ.
