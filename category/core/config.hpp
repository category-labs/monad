// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <bit>
#include <climits>

// ── KV DB prototype flag ────────────────────────────────────────────────
// Master compile-time switch for the separate flat KV-DB prototype (see
// ~/aaa/claude/260625/ design docs). Default 0 = baseline, untouched. Flip to
// 1 for proto builds. Placed here (not execution/db.hpp) so both the mpt/
// layer (which owns the io_uring service thread the KV read path runs on) and
// the execution/ layer can guard proto code on it — mpt is below execution and
// cannot include an execution header. Cost: flipping it rebuilds the tree.
// Uniquely greppable: KVDB_PROTO.
#define KVDB_PROTO 1

// Read-path metrics for the KV-DB prototype (per-node-read counters comparing
// trie db vs kv db: nodes traversed, cache hits, io reads). Compile-time so
// that when off the increments vanish entirely (no branch, no atomic), letting
// us rebuild both ways to confirm the counters don't distort timing. Only has
// effect when KVDB_PROTO is 1. Default on. Uniquely greppable: KVDB_METRICS.
#define KVDB_METRICS 1

// Device-layout boundary for the KV-DB prototype (kvdb_base separation).
// triedb keeps the WHOLE device (its pool is not shrunk, so existing archives
// restore unchanged); a hard guard in category/mpt/trie.cpp aborts if triedb
// ever allocates a seq chunk >= this index, keeping it out of KV's range. KV
// owns the device tail [phys(seq chunk KVDB_FIRST_SEQ_CHUNK), physical_end) as a
// FLAT array of fixed 4KB pages on its own fd (no chunks, no storage_pool). The
// *byte* offset of that boundary depends on the pool's cnv-chunk layout, so
// kvbuild queries the pool once for phys(seq chunk KVDB_FIRST_SEQ_CHUNK), writes
// KV there, and records it in the .kvhdr (KvHeader::base_offset); trie_db reads
// base_offset from the .kvhdr and does flat io at base_offset + ref. This value
// is the only cross-reference (kvbuild + the trie.cpp guard).
#define KVDB_FIRST_SEQ_CHUNK 4096u

// Multiversion (historical-block) support for the KV-DB prototype. KV keeps a
// ring of the last KVDB_HISTORY_N block roots so reads can be served at any
// block in [latest-N+1, latest] (mirrors triedb's external history interface;
// triedb's own floor is MIN_HISTORY_LENGTH=300, so N must be >= that). N=2048
// (~10 min at 300ms/block) is ~6.8x triedb's floor; worst-case retained size
// (append-only, no reclaim yet) ~= N * ~112MB/block ~= 224GB, ~27% of the
// ~835GB KV region. The ring lives in a reserved on-device metadata region at
// the FRONT of KV's range ([base_offset, base_offset+KVDB_META_BYTES)), so a
// future read-only reader process finds it by reading base_offset; kvbuild
// reserves it and node refs start at KVDB_META_BYTES. Uniquely greppable:
// KVDB_HISTORY_N, KVDB_META_BYTES.
#define KVDB_HISTORY_N 2048u
#define KVDB_META_BYTES 65536ull

#define MONAD_NAMESPACE_BEGIN                                                  \
    namespace monad                                                            \
    {

#define MONAD_NAMESPACE_END }

#define MONAD_NAMESPACE ::monad

#define MONAD_ANONYMOUS_NAMESPACE_BEGIN                                        \
    MONAD_NAMESPACE_BEGIN                                                      \
    namespace                                                                  \
    {

#define MONAD_ANONYMOUS_NAMESPACE_END                                          \
    }                                                                          \
    MONAD_NAMESPACE_END

static_assert(CHAR_BIT == 8);

static_assert(
    std::endian::native == std::endian::big ||
    std::endian::native == std::endian::little);

#if KVDB_PROTO

    #include <atomic>
    #include <cstdint>

// KV-DB prototype read-path metrics. Process-global counters comparing the trie
// db and kv db read paths on the same key stream (side by side in the shadow
// pass). Scope: execution read path only (RWDb resident-tree find + kv B+tree
// descent); the RPC / read-only path is out of scope until item (1).
//
// Metric = nodes traversed per lookup until the value is returned, counted the
// SAME way on both sides. A kv storage lookup traverses the account tree then
// the storage subtree; both descents SUM into one per-lookup number, matching
// the trie's single continuous descent.
//
// EVERY lookup is counted (empty/absent ones traverse nodes and hit caches +
// disk too), partitioned into found vs not-found buckets rather than filtered:
//   trie_acct_empty / trie_acct_nonempty, trie_stor_zero / trie_stor_nonzero,
//   and the same four for kv; plus trie_code, trie_other (untagged finds),
//   kv_prefetch (commit-path warm reads). The script sums these into the
//   account / storage / combined and value / no-value rows.
// Per bucket (all raw; derived downstream by a script):
//   reads     = lookups landing in this bucket
//   depth_sum = sum of per-lookup total depths (avg = depth_sum/reads)
//   max_depth = deepest lookup
//   hits/io_reads = node cache hits / device reads over the traversed nodes
// Counting sites: trie -> find_notify_fiber.cpp (per node) + db.cpp rwdb_run
// (root + begin); kv -> kv_read_node/kv_to_leaf/kv_deliver_slot in trie_db.cpp.
// Readout: the TrieDb dtor. Defined here (prototype-flag home, seen by both the
// mpt and execution layers) so the prototype stays in existing files. Single
// writer in practice (the DB io service thread); relaxed atomics keep the dtor's
// cross-thread read well-defined.
MONAD_NAMESPACE_BEGIN

namespace kvdb_metrics
{
    struct ReadCounters
    {
        std::atomic<uint64_t> reads{0};
        std::atomic<uint64_t> depth_sum{0};
        std::atomic<uint32_t> max_depth{0};
        std::atomic<uint64_t> hits{0};
        std::atomic<uint64_t> io_reads{0};

        // Record one completed lookup: depth = total nodes traversed, io = of
        // those, how many were device reads (so hits = depth - io).
        void add(uint32_t const depth, uint32_t const io)
        {
            reads.fetch_add(1, std::memory_order_relaxed);
            depth_sum.fetch_add(depth, std::memory_order_relaxed);
            io_reads.fetch_add(io, std::memory_order_relaxed);
            hits.fetch_add(depth - io, std::memory_order_relaxed);
            uint32_t cur = max_depth.load(std::memory_order_relaxed);
            while (depth > cur && !max_depth.compare_exchange_weak(
                                      cur, depth, std::memory_order_relaxed)) {
            }
        }
    };

    enum class LookupKind : uint8_t
    {
        other = 0,
        acct,
        stor,
        code
    };

    inline ReadCounters trie_acct_empty;
    inline ReadCounters trie_acct_nonempty;
    inline ReadCounters trie_stor_zero;
    inline ReadCounters trie_stor_nonzero;
    inline ReadCounters trie_code;
    inline ReadCounters trie_other;
    inline ReadCounters kv_acct_empty;
    inline ReadCounters kv_acct_nonempty;
    inline ReadCounters kv_stor_zero;
    inline ReadCounters kv_stor_nonzero;
    inline ReadCounters kv_code;
    // Commit-path prefetch descents (warm the cache before the build). Not a
    // lookup; kept separate so the read comparison stays clean.
    inline ReadCounters kv_prefetch;

    // Worker-thread descent state for the trie find path: the found / not-found
    // buckets for this lookup kind, plus depth and device-read (io) counts so
    // far. Set at find entry (db.cpp rwdb_run) and restored by the async
    // continuation (a device miss yields the worker thread to other in-flight
    // finds before the descent resumes). Its own thread (the DB io service
    // thread) => plain, not atomic.
    struct TrieDescent
    {
        ReadCounters *found;
        ReadCounters *notfound;
        uint32_t depth;
        uint32_t io;
    };

    inline thread_local TrieDescent cur_trie{
        &trie_acct_nonempty, &trie_acct_empty, 0, 0};

    inline void begin_trie(LookupKind const k)
    {
        switch (k) {
        case LookupKind::acct:
            cur_trie = {&trie_acct_nonempty, &trie_acct_empty, 0, 0};
            break;
        case LookupKind::stor:
            cur_trie = {&trie_stor_nonzero, &trie_stor_zero, 0, 0};
            break;
        case LookupKind::code:
            cur_trie = {&trie_code, &trie_code, 0, 0};
            break;
        default:
            cur_trie = {&trie_other, &trie_other, 0, 0};
            break;
        }
    }

    // Exec-fiber tag: read_account/read_storage/read_code set it before db_.find;
    // the find dispatch (db.cpp find_fiber_blocking) consumes-and-clears it into
    // the request's kind. Set and consumed on the same fiber with no yield in
    // between, so a plain thread_local is safe.
    inline thread_local LookupKind find_kind{LookupKind::other};
}

MONAD_NAMESPACE_END

#endif // KVDB_PROTO

// KVDB_TRIE_BEGIN(kind): start a trie descent for lookup `kind` (pick buckets,
//   reset depth/io).
// KVDB_TRIE_HIT() / KVDB_TRIE_IO(): count one node reached from the node cache /
//   from a device read.
// KVDB_TRIE_FOUND() / KVDB_TRIE_NOTFOUND(): the descent ended with / without a
//   value; record it on the matching bucket.
// KVDB_ADD(ref, depth, io): record a completed kv lookup (ref = a ReadCounters).
// All expand to nothing when compiled out, so counting sites need no #if guard.
#if KVDB_PROTO && KVDB_METRICS
    #define KVDB_TRIE_BEGIN(kind) ::monad::kvdb_metrics::begin_trie(kind)
    #define KVDB_TRIE_HIT() (void)(++::monad::kvdb_metrics::cur_trie.depth)
    #define KVDB_TRIE_IO()                                                     \
        do {                                                                   \
            ++::monad::kvdb_metrics::cur_trie.depth;                           \
            ++::monad::kvdb_metrics::cur_trie.io;                              \
        } while (0)
    #define KVDB_TRIE_FOUND()                                                  \
        (::monad::kvdb_metrics::cur_trie.found)                                \
            ->add(::monad::kvdb_metrics::cur_trie.depth,                       \
                  ::monad::kvdb_metrics::cur_trie.io)
    #define KVDB_TRIE_NOTFOUND()                                               \
        (::monad::kvdb_metrics::cur_trie.notfound)                             \
            ->add(::monad::kvdb_metrics::cur_trie.depth,                       \
                  ::monad::kvdb_metrics::cur_trie.io)
    #define KVDB_ADD(ref, depth, io) ((ref).add((depth), (io)))
#else
    #define KVDB_TRIE_BEGIN(kind) ((void)0)
    #define KVDB_TRIE_HIT() ((void)0)
    #define KVDB_TRIE_IO() ((void)0)
    #define KVDB_TRIE_FOUND() ((void)0)
    #define KVDB_TRIE_NOTFOUND() ((void)0)
    #define KVDB_ADD(ref, depth, io) ((void)0)
#endif
