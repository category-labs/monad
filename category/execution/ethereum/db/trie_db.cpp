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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.h>
#include <category/core/keccak.hpp>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/fmt/int_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/proposal_post_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/nibbles_view_fmt.hpp> // NOLINT
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine_kind.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <algorithm>
#include <atomic>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <format>
#include <limits>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <utility>
#include <vector>

#if KVDB_PROTO
    #include <category/async/io.hpp> // AsyncIO (io thread + post_to_io_thread)
    #include <category/core/io/buffer_pool.hpp> // BufferPool (KV's own io)
    #include <category/core/io/buffers.hpp> // Buffers, make_buffers_*
    #include <category/core/io/ring.hpp> // Ring (KV's own io_uring; pulls liburing)
    #include <category/core/lru/static_lru_cache.hpp>

    #include <boost/fiber/future.hpp> // promise/future for the exec-fiber wait

    #include <array>
    #include <cstdio>
    #include <deque>
    #include <functional> // std::move_only_function
    #include <map>

    #include <fcntl.h>
    #include <sys/mman.h>
    #include <unistd.h>
#endif

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

#if KVDB_PROTO
// ── KV-DB prototype: read-side shadow reader over a bulk-built KV image ──
// Node format + descent duplicated from cmd/kvbuild/main.cpp (prototype; dup
// accepted per the working plan). Read-only: descend the mmap'd image for an
// account / slot. See ~/aaa/claude/260625/build_tool_260701.md for the format.
namespace
{
    namespace kv
    {
        constexpr size_t NODE_SIZE = 4096;
        constexpr size_t HDR = 8;
        constexpr uint64_t NULL_REF = ~uint64_t{0};
        enum : uint8_t
        {
            N_INTERNAL = 0,
            N_LEAF_ACCOUNT = 1,
            N_LEAF_STORAGE_FLAT = 2,
            N_LEAF_STORAGE_PAGE = 3,
            // The account-tree ROOT, packed with this block's per-block blob
            // refs in its tail. Byte-identical to N_INTERNAL for descent (entries
            // at HDR); the tail [BLOCK_ROOT_BLOB_OFF, NODE_SIZE) holds BLOB_N 8B
            // blob roots. It is the single HP2-protected, separately-retired
            // block root; the state (its account children) and the blobs are its
            // ordinary link-counted children.
            N_BLOCK_ROOT = 4,
        };
        // Per-block ancillary blob categories packed into the block root tail;
        // NULL_REF when absent (that read falls back to triedb).
        enum BlobCat
        {
            BLOB_RECEIPTS = 0,
            BLOB_TXNS,
            BLOB_HEADER,
            BLOB_CALLFRAMES,
            BLOB_OMMERS,
            BLOB_WITHDRAWALS,
            BLOB_TXHASHES, // per-block list of tx hashes, for tx-index prune
        };
        constexpr size_t BLOB_N = 7;
        constexpr size_t BLOCK_ROOT_BLOB_OFF = NODE_SIZE - BLOB_N * 8; // tail
        struct BlobRoots
        {
            uint64_t r[BLOB_N];
            BlobRoots()
            {
                for (auto &x : r) {
                    x = NULL_REF;
                }
            }
        };
        constexpr size_t ACCT_KEY = 20; // address key length
        constexpr size_t STOR_KEY = 32; // slot / page_base key length
        constexpr size_t ACCT_REC = 20 + sizeof(Account) + 8; // 108
        constexpr size_t STOR_REC_FLAT = 64;
        constexpr size_t PG_BASE = 0; // page record: page_base at offset 0
        constexpr size_t PG_BITMAP = 32;
        constexpr size_t PG_FLAG = 48;
        constexpr size_t PG_PAYLOAD = 49;
        constexpr uint64_t MAGIC = 0x314256'4b'2d64766bULL;

        // KV owns a flat array of 4KB pages on its own fd at device offset
        // base_offset + ref, where base_offset (from the .kvhdr) = phys(seq
        // chunk KVDB_FIRST_SEQ_CHUNK). No storage_pool chunk geometry at runtime.

        // Raw 4KB device nodes keyed by logical node_ref (nodes built this block
        // live in the RAM write buffer, not here). A live ref's bytes never
        // change; reuse rewrites the entry, so no cache invalidation is needed.
        using NodeCache =
            static_lru_cache<uint64_t, std::array<unsigned char, NODE_SIZE>>;

        struct KvHeader
        {
            uint64_t magic;
            uint32_t version;
            uint32_t node_size;
            uint64_t root_ref;
            uint64_t node_count;
            uint64_t image_bytes;
            uint64_t num_accounts;
            uint64_t num_slots;
            uint32_t storage_format;
            uint32_t pad;
            uint64_t ext_nodes;
            // kvdb_base: device byte offset of node_ref 0 = phys(seq chunk
            // KVDB_FIRST_SEQ_CHUNK), computed by kvbuild from the pool. KV reads
            // flat at base_offset + ref. 0 for a plain-file image. (Layout MUST
            // match cmd/kvbuild's KvHeader.)
            uint64_t base_offset;
        };

        // kvdb_base multiversion: on-device metadata region at the FRONT of KV's
        // range ([base_offset, base_offset + KVDB_META_BYTES)). Header on page 0,
        // then a ring of history_n block roots at byte offset META_RING_OFF. A
        // read at block K resolves ring[K % history_n] iff lower_bound <= K <=
        // latest. mmap'd RW by execution for atomic per-block publish; a future
        // read-only reader finds it by reading base_offset. (Layout MUST match
        // cmd/kvbuild's KvMeta.)
        struct KvMeta
        {
            uint64_t magic; // META_MAGIC
            uint32_t version; // 7 (v7: adds tx-hash / block-hash index roots)
            uint32_t node_size; // == NODE_SIZE (sanity)
            uint64_t tree_root; // block map root ref
            uint64_t code_tree_root; // code index B+tree root (grow-only)
            // Global cumulative hash indexes (blockmap B+trees, own roots; COW +
            // link-counted + hazard-gated like the block map). Resolution-only:
            // tx_hash(32B) -> (block 8B, tx_index 4B); block_hash(32B) -> number
            // (8B). Inserted per block at commit, entries deleted at prune.
            uint64_t txhash_index_root;
            uint64_t blockhash_index_root;
            uint64_t finalized_block; // finalized tip block
            uint64_t oldest_block; // oldest finalized block still retained
            unsigned char finalized_id[32]; // finalized tip id
            // Consensus commit-state cursors (mirror triedb's latest_{proposed,
            // voted}_version/_block_id). Each names the canonical (block, id)
            // among possibly several proposals at that height; block == NONE
            // (UINT64_MAX) until consensus first stamps it. Read authority for
            // RPC's `latest` (proposed) and `safe` (voted) tags.
            uint64_t proposed_block; // latest proposed (canonical head)
            unsigned char proposed_id[32];
            uint64_t voted_block; // latest voted (safe)
            unsigned char voted_id[32];
            // Seqlock over the (block, id) cursor pairs above. Odd = a write is
            // in progress. A pair cannot be validated by re-reading either of
            // its own fields: the two stores are not atomic as a unit, so
            // whichever field is written first can be seen paired with the
            // other field's previous value, in either store order. Appended
            // last, so it reads as 0 (even, unlocked) in an image written
            // before it existed -- no format version bump needed.
            uint64_t tag_seq;
        };
        // "no cursor yet" sentinel for proposed_block / voted_block.
        constexpr uint64_t KV_BLOCK_NONE = ~uint64_t{0};
        constexpr uint64_t META_MAGIC = 0x31564d'4b'2d64766bULL;
        enum : uint8_t
        {
            N_BLOCKMAP_INTERNAL = 5,
            N_BLOCKMAP_LEAF = 6,
            N_CODE_INLINE = 7, // code root page holding the whole code
            N_CODE_INDEX = 8, // code root page pointing to raw data pages
            N_BLOB_INLINE = 9, // per-block blob wholly in the page (link-counted)
            N_BLOB_INDEX = 10, // blob root -> raw data pages (single blob > 1 page)
            N_BLOB_TABLE = 11, // per-block table: entry i -> blob root (per-tx)
        };
        static_assert(sizeof(KvMeta) <= NODE_SIZE);

        // ── multiversion block map: copy-on-write B+tree ─────────────────
        // One on-device B+tree maps a version key (block big-endian 8B, id 32B)
        // to (state_root 8B, parent_id 32B). Ordered by block then id, so a
        // finalized block is found by lower_bound(block, 0). Pages are 4KB,
        // written once at a fresh ref and never mutated: every insert/unlink
        // copies the path from the touched leaf to a new root.
        //   Internal page: [hdr][nc child refs 8B][nc-1 separators key_len];
        //     child i holds keys < separator[i], the last child the rest.
        //   Leaf page: [hdr][count entries, each key_len + val_len].
        // Generic over a page Store:
        //   unsigned char const *read(uint64_t ref);  // 4KB page for ref
        //   uint64_t emit(unsigned char const *page); // append, return new ref
        // Internal ops snapshot a node's contents before recursing, since a
        // nested emit() may invalidate an outstanding read() pointer.
        namespace blockmap
        {
            constexpr size_t BP_TYPE = 0, BP_KEYLEN = 1, BP_VALLEN = 2,
                             BP_COUNT = 4, BP_HDR = 8;

            [[maybe_unused]] inline uint16_t
            count_of(unsigned char const *const p)
            {
                uint16_t c;
                std::memcpy(&c, p + BP_COUNT, 2);
                return c;
            }
            [[maybe_unused]] inline bool is_leaf(unsigned char const *const p)
            {
                return p[BP_TYPE] == N_BLOCKMAP_LEAF;
            }
            [[maybe_unused]] inline size_t
            leaf_cap(size_t const kl, size_t const vl)
            {
                return (NODE_SIZE - BP_HDR) / (kl + vl);
            }
            [[maybe_unused]] inline size_t internal_cap(size_t const kl)
            {
                return (NODE_SIZE - BP_HDR + kl) / (8 + kl);
            }
            [[maybe_unused]] inline unsigned char const *leaf_key(
                unsigned char const *const p, size_t const i, size_t const kl,
                size_t const vl)
            {
                return p + BP_HDR + i * (kl + vl);
            }
            [[maybe_unused]] inline unsigned char const *leaf_val(
                unsigned char const *const p, size_t const i, size_t const kl,
                size_t const vl)
            {
                return leaf_key(p, i, kl, vl) + kl;
            }
            [[maybe_unused]] inline uint64_t
            child_ref(unsigned char const *const p, size_t const i)
            {
                uint64_t r;
                std::memcpy(&r, p + BP_HDR + i * 8, 8);
                return r;
            }
            [[maybe_unused]] inline unsigned char const *sep_key(
                unsigned char const *const p, size_t const i, size_t const nc,
                size_t const kl)
            {
                return p + BP_HDR + nc * 8 + i * kl;
            }
            [[maybe_unused]] inline size_t leaf_lb(
                unsigned char const *const p, unsigned char const *const key,
                size_t const kl, size_t const vl)
            {
                size_t lo = 0, hi = count_of(p);
                while (lo < hi) {
                    size_t const m = (lo + hi) / 2;
                    if (std::memcmp(leaf_key(p, m, kl, vl), key, kl) < 0) {
                        lo = m + 1;
                    }
                    else {
                        hi = m;
                    }
                }
                return lo;
            }
            [[maybe_unused]] inline size_t child_index(
                unsigned char const *const p, unsigned char const *const key,
                size_t const kl)
            {
                uint16_t const nc = count_of(p);
                size_t lo = 0, hi = nc - 1;
                while (lo < hi) {
                    size_t const m = (lo + hi) / 2;
                    if (std::memcmp(sep_key(p, m, nc, kl), key, kl) <= 0) {
                        lo = m + 1;
                    }
                    else {
                        hi = m;
                    }
                }
                return lo;
            }

            template <class Store>
            uint64_t emit_leaf(
                Store &s, unsigned char const *const buf, size_t const n,
                size_t const kl, size_t const vl)
            {
                std::array<unsigned char, NODE_SIZE> pg{};
                pg[BP_TYPE] = N_BLOCKMAP_LEAF;
                pg[BP_KEYLEN] = static_cast<unsigned char>(kl);
                pg[BP_VALLEN] = static_cast<unsigned char>(vl);
                uint16_t const c = static_cast<uint16_t>(n);
                std::memcpy(pg.data() + BP_COUNT, &c, 2);
                std::memcpy(pg.data() + BP_HDR, buf, n * (kl + vl));
                return s.emit(pg.data());
            }
            template <class Store>
            uint64_t emit_internal(
                Store &s, uint64_t const *const ch, unsigned char const *const sp,
                size_t const nc, size_t const kl)
            {
                std::array<unsigned char, NODE_SIZE> pg{};
                pg[BP_TYPE] = N_BLOCKMAP_INTERNAL;
                pg[BP_KEYLEN] = static_cast<unsigned char>(kl);
                uint16_t const c = static_cast<uint16_t>(nc);
                std::memcpy(pg.data() + BP_COUNT, &c, 2);
                std::memcpy(pg.data() + BP_HDR, ch, nc * 8);
                std::memcpy(pg.data() + BP_HDR + nc * 8, sp, (nc - 1) * kl);
                return s.emit(pg.data());
            }

            // exact-match lookup; copies value out if found
            template <class Store>
            bool lookup(
                Store &s, uint64_t ref, unsigned char const *const key,
                size_t const kl, size_t const vl, unsigned char *const out_val)
            {
                for (;;) {
                    unsigned char const *const p = s.read(ref);
                    if (is_leaf(p)) {
                        size_t const i = leaf_lb(p, key, kl, vl);
                        if (i < count_of(p) &&
                            std::memcmp(leaf_key(p, i, kl, vl), key, kl) == 0) {
                            if (out_val) {
                                std::memcpy(
                                    out_val, leaf_val(p, i, kl, vl), vl);
                            }
                            return true;
                        }
                        return false;
                    }
                    ref = child_ref(p, child_index(p, key, kl));
                }
            }

            // smallest entry with key >= `key`; copies key+value out (finalized
            // read: lower_bound(block,0), then check the returned block matches)
            template <class Store>
            bool lower_bound(
                Store &s, uint64_t const ref, unsigned char const *const key,
                size_t const kl, size_t const vl, unsigned char *const ok,
                unsigned char *const ov)
            {
                unsigned char const *const p = s.read(ref);
                if (is_leaf(p)) {
                    size_t const i = leaf_lb(p, key, kl, vl);
                    if (i >= count_of(p)) {
                        return false;
                    }
                    std::memcpy(ok, leaf_key(p, i, kl, vl), kl);
                    std::memcpy(ov, leaf_val(p, i, kl, vl), vl);
                    return true;
                }
                size_t const ci = child_index(p, key, kl);
                uint16_t const nc = count_of(p);
                uint64_t const child = child_ref(p, ci);
                uint64_t const next =
                    (ci + 1 < nc) ? child_ref(p, ci + 1) : NULL_REF;
                if (lower_bound(s, child, key, kl, vl, ok, ov)) {
                    return true;
                }
                if (next != NULL_REF) { // leftmost entry of the next child
                    uint64_t r = next;
                    for (;;) {
                        unsigned char const *const q = s.read(r);
                        if (is_leaf(q)) {
                            if (count_of(q) == 0) {
                                return false;
                            }
                            std::memcpy(ok, leaf_key(q, 0, kl, vl), kl);
                            std::memcpy(ov, leaf_val(q, 0, kl, vl), vl);
                            return true;
                        }
                        r = child_ref(q, 0);
                    }
                }
                return false;
            }

            // callback for every entry with lo <= key <= hi (finalize: a whole
            // block's key range)
            template <class Store, class F>
            void scan_range(
                Store &s, uint64_t const ref, unsigned char const *const lo,
                unsigned char const *const hi, size_t const kl, size_t const vl,
                F &&cb)
            {
                unsigned char const *const p = s.read(ref);
                if (is_leaf(p)) {
                    uint16_t const n = count_of(p);
                    for (size_t i = 0; i < n; ++i) {
                        unsigned char const *const k = leaf_key(p, i, kl, vl);
                        if (std::memcmp(k, lo, kl) >= 0 &&
                            std::memcmp(k, hi, kl) <= 0) {
                            cb(k, k + kl);
                        }
                    }
                    return;
                }
                uint16_t const nc = count_of(p);
                std::vector<uint64_t> ch(nc);
                for (size_t i = 0; i < nc; ++i) {
                    ch[i] = child_ref(p, i);
                }
                std::vector<unsigned char> sp(static_cast<size_t>(nc - 1) * kl);
                if (nc > 1) {
                    std::memcpy(sp.data(), sep_key(p, 0, nc, kl), (nc - 1) * kl);
                }
                for (size_t i = 0; i < nc; ++i) {
                    if (i > 0 &&
                        std::memcmp(sp.data() + (i - 1) * kl, hi, kl) > 0) {
                        continue;
                    }
                    if (i + 1 < nc &&
                        std::memcmp(sp.data() + i * kl, lo, kl) <= 0) {
                        continue;
                    }
                    scan_range(s, ch[i], lo, hi, kl, vl, cb);
                }
            }

            // COW insert/upsert. On a node split, sets *split and returns the
            // promoted separator + new right sibling via out params.
            template <class Store>
            uint64_t insert_rec(
                Store &s, uint64_t const ref, unsigned char const *const key,
                unsigned char const *const val, size_t const kl, size_t const vl,
                bool *const split, unsigned char *const sep_out,
                uint64_t *const right_out)
            {
                unsigned char const *const p = s.read(ref);
                size_t const esz = kl + vl;
                if (is_leaf(p)) {
                    uint16_t const n = count_of(p);
                    size_t const pos = leaf_lb(p, key, kl, vl);
                    bool const exists =
                        pos < n &&
                        std::memcmp(leaf_key(p, pos, kl, vl), key, kl) == 0;
                    std::vector<unsigned char> buf(
                        static_cast<size_t>(n + 1) * esz);
                    std::memcpy(
                        buf.data(), p + BP_HDR, static_cast<size_t>(n) * esz);
                    size_t m = n;
                    if (exists) {
                        std::memcpy(buf.data() + pos * esz + kl, val, vl);
                    }
                    else {
                        std::memmove(
                            buf.data() + (pos + 1) * esz,
                            buf.data() + pos * esz, (n - pos) * esz);
                        std::memcpy(buf.data() + pos * esz, key, kl);
                        std::memcpy(buf.data() + pos * esz + kl, val, vl);
                        m = n + 1;
                    }
                    if (m <= leaf_cap(kl, vl)) {
                        *split = false;
                        return emit_leaf(s, buf.data(), m, kl, vl);
                    }
                    size_t const l = m / 2; // overflow: split
                    uint64_t const left = emit_leaf(s, buf.data(), l, kl, vl);
                    *right_out =
                        emit_leaf(s, buf.data() + l * esz, m - l, kl, vl);
                    std::memcpy(sep_out, buf.data() + l * esz, kl);
                    *split = true;
                    return left;
                }
                uint16_t const nc = count_of(p);
                size_t const ci = child_index(p, key, kl);
                std::vector<uint64_t> ch(nc); // snapshot before recursing
                for (size_t i = 0; i < nc; ++i) {
                    ch[i] = child_ref(p, i);
                }
                std::vector<unsigned char> sp(static_cast<size_t>(nc - 1) * kl);
                if (nc > 1) {
                    std::memcpy(sp.data(), sep_key(p, 0, nc, kl), (nc - 1) * kl);
                }
                bool cs = false;
                std::vector<unsigned char> csep(kl);
                uint64_t cr = NULL_REF;
                uint64_t const nch = insert_rec(
                    s, ch[ci], key, val, kl, vl, &cs, csep.data(), &cr);
                ch[ci] = nch;
                if (!cs) {
                    *split = false;
                    return emit_internal(s, ch.data(), sp.data(), nc, kl);
                }
                ch.insert(ch.begin() + ci + 1, cr);
                sp.insert(sp.begin() + ci * kl, csep.begin(), csep.end());
                size_t const mc = nc + 1;
                if (mc <= internal_cap(kl)) {
                    *split = false;
                    return emit_internal(s, ch.data(), sp.data(), mc, kl);
                }
                size_t const lc = mc / 2; // split, promote separator[lc-1]
                std::memcpy(sep_out, sp.data() + (lc - 1) * kl, kl);
                uint64_t const left =
                    emit_internal(s, ch.data(), sp.data(), lc, kl);
                *right_out = emit_internal(
                    s, ch.data() + lc, sp.data() + lc * kl, mc - lc, kl);
                *split = true;
                return left;
            }

            template <class Store>
            uint64_t insert(
                Store &s, uint64_t const root, unsigned char const *const key,
                unsigned char const *const val, size_t const kl, size_t const vl)
            {
                bool split = false;
                std::vector<unsigned char> sep(kl);
                uint64_t right = NULL_REF;
                uint64_t const nr = insert_rec(
                    s, root, key, val, kl, vl, &split, sep.data(), &right);
                if (!split) {
                    return nr;
                }
                uint64_t const ch[2] = {nr, right}; // root split: new root
                return emit_internal(s, ch, sep.data(), 2, kl);
            }

            // COW delete of one key. Drops a node from its parent when it
            // becomes empty; does NOT merge/borrow underfull nodes (reclamation
            // reclaims space later).
            template <class Store>
            uint64_t unlink_rec(
                Store &s, uint64_t const ref, unsigned char const *const key,
                size_t const kl, size_t const vl, bool *const removed)
            {
                unsigned char const *const p = s.read(ref);
                size_t const esz = kl + vl;
                if (is_leaf(p)) {
                    uint16_t const n = count_of(p);
                    size_t const pos = leaf_lb(p, key, kl, vl);
                    if (!(pos < n &&
                          std::memcmp(leaf_key(p, pos, kl, vl), key, kl) == 0)) {
                        *removed = false;
                        return ref; // absent: no-op
                    }
                    if (n == 1) {
                        *removed = true;
                        return NULL_REF; // leaf now empty
                    }
                    std::vector<unsigned char> buf(
                        static_cast<size_t>(n - 1) * esz);
                    std::memcpy(buf.data(), p + BP_HDR, pos * esz);
                    std::memcpy(
                        buf.data() + pos * esz, p + BP_HDR + (pos + 1) * esz,
                        (n - 1 - pos) * esz);
                    *removed = false;
                    return emit_leaf(s, buf.data(), n - 1, kl, vl);
                }
                uint16_t const nc = count_of(p);
                size_t const ci = child_index(p, key, kl);
                std::vector<uint64_t> ch(nc); // snapshot before recursing
                for (size_t i = 0; i < nc; ++i) {
                    ch[i] = child_ref(p, i);
                }
                std::vector<unsigned char> sp(static_cast<size_t>(nc - 1) * kl);
                if (nc > 1) {
                    std::memcpy(sp.data(), sep_key(p, 0, nc, kl), (nc - 1) * kl);
                }
                uint64_t const old_ci = ch[ci];
                bool crem = false;
                uint64_t const nch = unlink_rec(s, old_ci, key, kl, vl, &crem);
                if (!crem && nch == old_ci) {
                    *removed = false;
                    return ref; // no-op
                }
                if (crem) {
                    ch.erase(ch.begin() + ci);
                    if (nc >= 2) {
                        size_t const si = ci ? ci - 1 : 0;
                        sp.erase(
                            sp.begin() + si * kl, sp.begin() + (si + 1) * kl);
                    }
                    if (ch.empty()) {
                        *removed = true;
                        return NULL_REF;
                    }
                }
                else {
                    ch[ci] = nch;
                }
                *removed = false;
                return emit_internal(s, ch.data(), sp.data(), ch.size(), kl);
            }

            template <class Store>
            uint64_t unlink(
                Store &s, uint64_t const root, unsigned char const *const key,
                size_t const kl, size_t const vl)
            {
                bool removed = false;
                uint64_t const nr = unlink_rec(s, root, key, kl, vl, &removed);
                if (removed) { // whole tree empty: fresh empty leaf
                    std::array<unsigned char, NODE_SIZE> pg{};
                    pg[BP_TYPE] = N_BLOCKMAP_LEAF;
                    pg[BP_KEYLEN] = static_cast<unsigned char>(kl);
                    pg[BP_VALLEN] = static_cast<unsigned char>(vl);
                    return s.emit(pg.data());
                }
                unsigned char const *const p = s.read(nr);
                if (!is_leaf(p) && count_of(p) == 1) {
                    return child_ref(p, 0); // collapse a 1-child root
                }
                return nr;
            }
        } // namespace blockmap

        // ── block map self-check (validation only; KVDB_BMTEST=1) ─────────
        // Drives the block map against an in-memory store and cross-checks
        // every operation with a reference std::map, then exits. Independent of
        // triedb; catches split/unlink/collapse bugs directly.
        struct MemStore
        {
            std::vector<std::array<unsigned char, NODE_SIZE>> pages;
            std::array<unsigned char, NODE_SIZE> buf;
            unsigned char const *read(uint64_t const ref)
            {
                std::memcpy(buf.data(), pages[ref].data(), NODE_SIZE);
                return buf.data();
            }
            uint64_t emit(unsigned char const *const page)
            {
                pages.emplace_back();
                std::memcpy(pages.back().data(), page, NODE_SIZE);
                return pages.size() - 1;
            }
        };

        inline uint64_t bmtest_block(unsigned char const *const k)
        {
            uint64_t b = 0;
            for (int i = 0; i < 8; ++i) {
                b = (b << 8) | k[i];
            }
            return b;
        }

        inline void bmtest()
        {
            constexpr size_t KL = 40, VL = 40;
            MemStore s;
            std::array<unsigned char, NODE_SIZE> pg{};
            pg[blockmap::BP_TYPE] = N_BLOCKMAP_LEAF;
            pg[blockmap::BP_KEYLEN] = KL;
            pg[blockmap::BP_VALLEN] = VL;
            uint64_t root = s.emit(pg.data());

            std::map<std::array<unsigned char, KL>, std::array<unsigned char, VL>>
                ref;
            uint64_t rng = 0x9e3779b97f4a7c15ULL;
            auto next = [&]() {
                rng = rng * 6364136223846793005ULL + 1442695040888963407ULL;
                return rng >> 17;
            };
            auto mkkey = [&](std::array<unsigned char, KL> &k) {
                uint64_t const blk = next() % 64; // small range => many siblings
                for (int i = 0; i < 8; ++i) {
                    k[i] = static_cast<unsigned char>(blk >> (56 - 8 * i));
                }
                for (int i = 8; i < static_cast<int>(KL); ++i) {
                    k[i] = static_cast<unsigned char>(next());
                }
            };

            for (int i = 0; i < 200000; ++i) {
                std::array<unsigned char, KL> k;
                mkkey(k);
                unsigned const op = next() % 4;
                if (op == 0 || op == 1) { // insert / upsert
                    std::array<unsigned char, VL> v;
                    for (int j = 0; j < static_cast<int>(VL); ++j) {
                        v[j] = static_cast<unsigned char>(next());
                    }
                    root = blockmap::insert(s, root, k.data(), v.data(), KL, VL);
                    ref[k] = v;
                }
                else if (op == 2) { // unlink
                    root = blockmap::unlink(s, root, k.data(), KL, VL);
                    ref.erase(k);
                }
                else { // lookup + lower_bound cross-check
                    unsigned char v[VL];
                    bool const got =
                        blockmap::lookup(s, root, k.data(), KL, VL, v);
                    auto it = ref.find(k);
                    MONAD_ASSERT(got == (it != ref.end()));
                    if (got) {
                        MONAD_ASSERT(
                            std::memcmp(v, it->second.data(), VL) == 0);
                    }
                    unsigned char lbk[KL], lbv[VL];
                    bool const lb = blockmap::lower_bound(
                        s, root, k.data(), KL, VL, lbk, lbv);
                    auto ri = ref.lower_bound(k);
                    MONAD_ASSERT(lb == (ri != ref.end()));
                    if (lb) {
                        MONAD_ASSERT(
                            std::memcmp(lbk, ri->first.data(), KL) == 0);
                    }
                }
            }
            for (auto const &[k, v] : ref) { // every key present + correct
                unsigned char got[VL];
                MONAD_ASSERT(blockmap::lookup(s, root, k.data(), KL, VL, got));
                MONAD_ASSERT(std::memcmp(got, v.data(), VL) == 0);
            }
            for (uint64_t blk = 0; blk < 64; ++blk) { // scan_range vs ref
                std::array<unsigned char, KL> lo{}, hi{};
                for (int i = 0; i < 8; ++i) {
                    lo[i] = hi[i] = static_cast<unsigned char>(blk >> (56 - 8 * i));
                }
                for (int i = 8; i < static_cast<int>(KL); ++i) {
                    hi[i] = 0xff;
                }
                size_t n = 0;
                blockmap::scan_range(
                    s, root, lo.data(), hi.data(), KL, VL,
                    [&](unsigned char const *const kk, unsigned char const *) {
                        std::array<unsigned char, KL> a;
                        std::memcpy(a.data(), kk, KL);
                        MONAD_ASSERT(ref.count(a));
                        ++n;
                    });
                size_t exp = 0;
                for (auto const &[k, v] : ref) {
                    if (bmtest_block(k.data()) == blk) {
                        ++exp;
                    }
                }
                MONAD_ASSERT(n == exp);
            }
            std::fprintf(
                stderr, "KVDB_BMTEST ok: 200000 ops, %zu keys, %zu pages\n",
                ref.size(), s.pages.size());
        }

        inline bool bit_test(unsigned char const *const bm, size_t const idx)
        {
            return (bm[idx >> 3] >> (idx & 7)) & 1u;
        }

        inline size_t bit_rank(unsigned char const *const bm, size_t const idx)
        {
            size_t const full = idx >> 3;
            size_t const rem = idx & 7;
            size_t r = 0;
            for (size_t b = 0; b < full; ++b) {
                r += static_cast<size_t>(__builtin_popcount(bm[b]));
            }
            if (rem) {
                r += static_cast<size_t>(__builtin_popcount(
                    static_cast<unsigned>(bm[full]) & ((1u << rem) - 1)));
            }
            return r;
        }

        // Returns a node's 4KB bytes by ref during a commit. A ref is either one
        // of this block's freshly-built nodes (still in the RAM write buffer
        // `wbuf`, located via `wbuf_index`: ref -> wbuf index) or an
        // already-committed node read from the device (cache hit, else a
        // synchronous pread into the cache). Keyed by ref, not by position, so
        // reused (reclaimed) page refs that are non-contiguous work. Runs on the
        // DB io thread (single-thread cache access). Commit reads are mostly warm
        // cache hits from tx-exec; misses are rare, so pread is fine and not on
        // the read hot path.
        struct NodeReader
        {
            std::vector<std::array<unsigned char, NODE_SIZE>> const *wbuf;
            std::unordered_map<uint64_t, uint32_t> const *wbuf_index; // ref->idx
            NodeCache *cache;
            int kv_fd; // KV's own fd; committed nodes at base + ref
            uint64_t base; // device byte offset of node_ref 0 (from .kvhdr)

            unsigned char const *operator()(uint64_t const ref) const
            {
                if (auto const it = wbuf_index->find(ref);
                    it != wbuf_index->end()) {
                    // a node built this block (RAM write buffer)
                    return (*wbuf)[it->second].data();
                }
                NodeCache::ConstAccessor acc;
                if (cache->find(acc, ref)) {
                    return acc->second->val.data();
                }
                // Rare (prefetch warms this path): synchronous O_DIRECT pread,
                // so the buffer must be device-block-aligned (alignas(NODE_SIZE)
                // covers any logical sector <= 4KB).
                alignas(NODE_SIZE) std::array<unsigned char, NODE_SIZE> node;
                ssize_t const r = ::pread(
                    kv_fd,
                    node.data(),
                    NODE_SIZE,
                    static_cast<off_t>(base + ref));
                MONAD_ASSERT(r == static_cast<ssize_t>(NODE_SIZE));
                cache->insert(ref, node);
                NodeCache::ConstAccessor acc2;
                bool const hit = cache->find(acc2, ref);
                MONAD_ASSERT(hit);
                return acc2->second->val.data();
            }
        };

        uint64_t descend_to_leaf(
            NodeReader const &R, uint64_t root, unsigned char const *const key)
        {
            uint64_t ref = root;
            for (;;) {
                unsigned char const *n = R(ref);
                // N_BLOCK_ROOT descends like N_INTERNAL (entries at HDR); its
                // blob tail is past the entries and never reached here.
                if (n[0] != N_INTERNAL && n[0] != N_BLOCK_ROOT) {
                    return ref;
                }
                size_t const kl = n[1];
                uint16_t count;
                std::memcpy(&count, n + 2, sizeof(count));
                unsigned char const *p = n + HDR;
                size_t const esz = kl + 8;
                long chosen = -1;
                for (size_t i = 0; i < count; ++i) {
                    if (std::memcmp(p + i * esz, key, kl) <= 0) {
                        chosen = static_cast<long>(i);
                    }
                    else {
                        break;
                    }
                }
                // key below the first separator (e.g. an SLOAD of an absent
                // low slot) routes to the leftmost child; the leaf scan then
                // reports it absent. (Separators are valid child-mins, so a
                // present key is never below sep_0.)
                if (chosen < 0) {
                    chosen = 0;
                }
                std::memcpy(
                    &ref,
                    p + static_cast<size_t>(chosen) * esz + kl,
                    sizeof(ref));
            }
        }

        // account record ptr (addr,account,sref) or nullptr
        unsigned char const *find_account(
            NodeReader const &R, uint64_t const root, Address const &addr)
        {
            uint64_t const ref = descend_to_leaf(R, root, addr.bytes);
            unsigned char const *n = R(ref);
            MONAD_ASSERT(n[0] == N_LEAF_ACCOUNT);
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            unsigned char const *p = n + HDR;
            for (size_t i = 0; i < count; ++i) {
                unsigned char const *rec = p + i * ACCT_REC;
                if (std::memcmp(rec, addr.bytes, 20) == 0) {
                    return rec;
                }
            }
            return nullptr;
        }

        // (storage-leaf scan for reads now lives in the async path's
        // kv_deliver_slot; the sync find_slot was retired with the mmap reads.)

        // ── item 1: extract per-block updates from StateDeltas ──────────
        struct SlotUpdate
        {
            bytes32_t slot;
            bytes32_t value; // zero => remove the slot
        };

        enum class AcctOp
        {
            Set, // add or update: write `account`
            Delete, // remove the account (and its storage)
        };

        struct AccountUpdates
        {
            Address addr;
            AcctOp op;
            Account account; // valid iff op == Set
            std::vector<SlotUpdate> slots; // sorted by slot
        };

        // Separate, testable pass over StateDeltas -> raw KV updates (no
        // keccak / RLP / pages). `old` is used only to classify the op; `new`
        // (Delta::second) drives set-vs-delete / set-vs-remove.
        std::vector<AccountUpdates> extract_updates(StateDeltas const &deltas)
        {
            std::vector<AccountUpdates> out;
            out.reserve(deltas.size());
            for (auto const &entry : deltas) {
                std::optional<Account> const &na = entry.second.account.second;
                AccountUpdates au;
                au.addr = entry.first;
                // Only slots that actually changed (original != current);
                // read-but-unchanged slots must NOT be rewritten. Mirrors
                // CommitBuilder::add_state_deltas' `delta.first != delta.second`
                // guard (without it, commit re-writes untouched values).
                for (auto const &s : entry.second.storage) {
                    if (s.second.first != s.second.second) {
                        au.slots.push_back({s.first, s.second.second});
                    }
                }
                // Skip the account entirely when nothing changed (account
                // unchanged AND no changed slots) — same guard as triedb's
                // `!storage_updates.empty() || delta.account.first != account`.
                bool const account_changed =
                    entry.second.account.first != na;
                if (au.slots.empty() && !account_changed) {
                    continue;
                }
                if (!na.has_value() || is_empty(*na)) {
                    au.op = AcctOp::Delete;
                }
                else {
                    au.op = AcctOp::Set;
                    au.account = *na;
                }
                std::sort(
                    au.slots.begin(),
                    au.slots.end(),
                    [](SlotUpdate const &a, SlotUpdate const &b) {
                        return std::memcmp(a.slot.bytes, b.slot.bytes, 32) < 0;
                    });
                out.push_back(std::move(au));
            }
            std::sort(
                out.begin(),
                out.end(),
                [](AccountUpdates const &a, AccountUpdates const &b) {
                    return std::memcmp(a.addr.bytes, b.addr.bytes, 20) < 0;
                });
            return out;
        }

        // (key, ref) entry threaded up during bottom-up packing (item 2).
        struct LevelEnt
        {
            unsigned char key[STOR_KEY]; // uses key_len bytes
            uint64_t ref;
        };

        // Account-tree write: set the 108B record, or delete the account.
        struct AcctWrite
        {
            Address addr;
            bool del;
            std::array<unsigned char, ACCT_REC> rec; // valid iff !del
        };

        // ── item (2): async io_uring descent (production read path) ─────
        // Runs on the DB io service thread during KV's posted tasks. A cache
        // miss submits one 4KB node read to KvIo (KV's OWN io_uring, O_DIRECT,
        // registered buffers); the completion copies the node into the LRU cache
        // and resumes the descent. The caller drains KvIo to run descents to
        // completion. No AsyncIO, no storage_pool. (kvdb_base Stage 2.)

        using KeyBuf = std::array<unsigned char, STOR_KEY>;
        // Continuation invoked with a resolved node pointer + whether reaching
        // it required a device read (true) or was a cache hit (false).
        using NodeCont =
            std::move_only_function<void(unsigned char const *, bool)>;
        // Leaf continuation: the leaf node + the descent depth that reached it
        // and how many of those nodes were device reads (per-lookup totals; a
        // storage lookup continues its account descent's counts).
        using LeafCont = std::move_only_function<void(
            unsigned char const *, uint32_t, uint32_t)>;

        // Minimal single-threaded async io_uring engine for KV's flat page
        // store, built on the low-level io primitives (io::Ring/Buffers), NOT
        // AsyncIO: O_DIRECT, registered 4KB buffers, absolute-offset reads and
        // RANDOM-offset writes (random writes are the reclamation prerequisite).
        // Driven on the DB io thread inside KV's posted tasks: callers submit_*
        // then drain(). node_ref maps to device offset base + ref.
        struct KvIo
        {
            static constexpr unsigned RING_ENTRIES = 512;
            static constexpr size_t RD_BUFS = 1024;
            static constexpr size_t WR_BUFS = 1024;

            int fd;
            uint64_t base;
            NodeCache *cache;
            ::monad::io::Ring ring;
            ::monad::io::Buffers bufs;
            ::monad::io::BufferPool rd_pool;
            ::monad::io::BufferPool wr_pool;
            size_t in_flight{0};
            // Batched submit: submit_* prep SQEs and set this; flush() issues one
            // io_uring_submit for all of them (one syscall for many reads, vs one
            // per read). Flushed by the io loop each iteration and before waits.
            bool needs_submit{false};
            // Set true around the commit-time prefetch batch so its fan-out
            // reads don't pollute the serve-path pipeline-depth metric below.
            bool in_batch{false};
#if KVDB_METRICS
            // Peak concurrent in-flight SERVE reads (the tx-exec read pipeline
            // depth) and their counts, sampled in submit_read only when NOT in a
            // prefetch batch (in_batch=false).
            size_t max_read_in_flight{0};
            uint64_t reads_submitted{0};
            uint64_t reads_overlapped{0}; // submitted while another was in flight
#endif

            // Heap op recovered from the CQE user_data. Reads carry a
            // continuation; writes just release their registered buffer.
            struct Op
            {
                bool is_write;
                uint64_t ref; // read: node ref (cache key)
                unsigned char *buf; // registered 4KB slot
                NodeCont cont; // read only
            };

            KvIo(int const fd_, uint64_t const base_, NodeCache *const cache_)
                : fd{fd_}
                , base{base_}
                , cache{cache_}
                , ring{::monad::io::RingConfig{RING_ENTRIES}}
                , bufs{::monad::io::make_buffers_for_mixed_read_write(
                      ring, RD_BUFS, WR_BUFS, NODE_SIZE, NODE_SIZE)}
                , rd_pool{bufs, /*is_read_only=*/true}
                , wr_pool{bufs, /*is_read_only=*/false}
            {
            }

            io_uring *r() { return &ring.get_ring(); }

            // Reap one completion; dispatch it (a read caches the node and fires
            // its continuation, which may submit more reads). `block` waits for
            // one; else peeks (returns false if none ready).
            bool reap_one(bool const block)
            {
                io_uring_cqe *cqe = nullptr;
                if (block) {
                    io_uring_wait_cqe(r(), &cqe);
                }
                else if (io_uring_peek_cqe(r(), &cqe) != 0) {
                    return false;
                }
                void *const data = io_uring_cqe_get_data(cqe);
                int const res = cqe->res;
                io_uring_cqe_seen(r(), cqe);
                --in_flight;
                Op *const op = static_cast<Op *>(data);
                MONAD_ASSERT(res == static_cast<int>(NODE_SIZE));
                if (op->is_write) {
                    wr_pool.release(op->buf);
                    delete op;
                    return true;
                }
                std::array<unsigned char, NODE_SIZE> node;
                std::memcpy(node.data(), op->buf, NODE_SIZE);
                cache->insert(op->ref, node);
                rd_pool.release(op->buf);
                uint64_t const ref = op->ref;
                NodeCont cont = std::move(op->cont);
                delete op;
                NodeCache::ConstAccessor acc;
                bool const hit = cache->find(acc, ref);
                MONAD_ASSERT(hit);
                cont(acc->second->val.data(), /*was_device_read=*/true);
                return true;
            }

            // Free an SQ slot / a buffer by reaping if we're at capacity. With
            // RD/WR_BUFS >= any real batch these rarely reap; they are the
            // throttle for an unusually wide block.
            // Issue one io_uring_submit for all prepped-but-unsubmitted SQEs.
            void flush()
            {
                if (needs_submit) {
                    io_uring_submit(r());
                    needs_submit = false;
                }
            }
            // Get an SQE; if the SQ is full of un-submitted SQEs, flush to free
            // slots and retry.
            io_uring_sqe *get_sqe()
            {
                io_uring_sqe *sqe = io_uring_get_sqe(r());
                if (sqe == nullptr) {
                    flush();
                    sqe = io_uring_get_sqe(r());
                    MONAD_ASSERT(sqe != nullptr);
                }
                return sqe;
            }
            unsigned char *alloc_buf(::monad::io::BufferPool &pool)
            {
                unsigned char *buf = pool.alloc();
                while (buf == nullptr) {
                    MONAD_ASSERT(in_flight > 0);
                    flush(); // prepped reads must reach the kernel before we wait
                    reap_one(/*block=*/true);
                    buf = pool.alloc();
                }
                return buf;
            }

            void submit_read(uint64_t const ref, NodeCont cont)
            {
                unsigned char *const buf = alloc_buf(rd_pool);
                Op *const op = new Op{false, ref, buf, std::move(cont)};
                io_uring_sqe *const sqe = get_sqe();
                io_uring_prep_read_fixed(
                    sqe, fd, buf, NODE_SIZE, static_cast<off_t>(base + ref),
                    ::monad::io::Buffers::get_read_index());
                io_uring_sqe_set_data(sqe, op);
                needs_submit = true; // batched; flushed by the io loop / drain
#if KVDB_METRICS
                if (!in_batch) {
                    if (in_flight > 0) {
                        ++reads_overlapped;
                    }
                    ++reads_submitted;
                }
#endif
                ++in_flight;
#if KVDB_METRICS
                if (!in_batch && in_flight > max_read_in_flight) {
                    max_read_in_flight = in_flight;
                }
#endif
            }

            // Random-offset 4KB write (the node data is copied into a registered
            // write buffer). The offset is each node's own ref (wref_[i]), which
            // may be a reused reclaimed page, so writes are not contiguous.
            void
            submit_write(uint64_t const ref, unsigned char const *const data)
            {
                unsigned char *const buf = alloc_buf(wr_pool);
                std::memcpy(buf, data, NODE_SIZE);
                Op *const op = new Op{true, ref, buf, NodeCont{}};
                io_uring_sqe *const sqe = get_sqe();
                io_uring_prep_write_fixed(
                    sqe, fd, buf, NODE_SIZE, static_cast<off_t>(base + ref),
                    ::monad::io::Buffers::get_write_index());
                io_uring_sqe_set_data(sqe, op);
                needs_submit = true;
                ++in_flight;
            }

            void drain()
            {
                while (in_flight > 0) {
                    flush(); // prepped ops must reach the kernel before we wait
                    reap_one(/*block=*/true);
                }
            }

            // Non-blocking: dispatch every ready completion (continuations may
            // submit more), then return without waiting. Driven once per io-loop
            // iteration so reads from the parallel exec fibers pipeline instead
            // of draining one lookup at a time.
            void reap_ready()
            {
                flush(); // push this iteration's prepped reads to the kernel
                while (in_flight > 0 && reap_one(/*block=*/false)) {
                }
                flush(); // and any reads the dispatched continuations prepped
            }

            size_t outstanding() const { return in_flight; }
        };

        // KV read context: a handle to KvIo (owns fd, base, cache, ring).
        struct Ctx
        {
            KvIo *kvio;
        };

        // Cross-process hazard-pointer array in shared memory. A reader (the RPC
        // process, not built yet) publishes the roots it is reading -- HP1 = the
        // block-map root during the lookup, HP2 = the state root for the query -- so
        // the reclaim step defers freeing them. Exec creates + zeroes the segment and
        // scans it (collect). The reader-side acquire/publish/release also live here
        // (mm_hp-style lock-bit free list) and are exercised by the self-test, but
        // nothing calls them until the RPC process is wired. seq_cst throughout:
        // publish/scan is per-request (coarse), so the fence cost is irrelevant.
        struct HazardArray
        {
            static constexpr uint32_t MAX = 16384; // capacity ceiling (~2MB padded)
            static constexpr uint32_t NIL = 0; // empty list / slot 0 reserved
            static constexpr uint32_t LOCK = 0x80000000u; // avail pop-lock (bit 31)

            struct alignas(128) Entry
            {
                std::atomic<uint64_t> hp1;
                std::atomic<uint64_t> hp2;
                std::atomic<uint32_t> avail_next; // reader free-list link
            };
            struct Region
            {
                std::atomic<uint32_t> hcount; // slots handed out (bump; starts at 1)
                std::atomic<uint32_t> avail; // reader free-list head (lock in bit 31)
                Entry entries[MAX];
            };
            Region *r_ = nullptr;
            int fd_ = -1;

            // Exec: (re)create a zeroed segment; slot 0 is reserved so hcount=1.
            void create(char const *const name)
            {
                ::shm_unlink(name); // fresh each run (prototype)
                fd_ = ::shm_open(name, O_CREAT | O_RDWR, 0600);
                MONAD_ASSERT(fd_ != -1);
                MONAD_ASSERT(::ftruncate(fd_, (off_t)sizeof(Region)) == 0);
                void *const m = ::mmap(
                    nullptr, sizeof(Region), PROT_READ | PROT_WRITE, MAP_SHARED,
                    fd_, 0);
                MONAD_ASSERT(m != MAP_FAILED);
                r_ = static_cast<Region *>(m);
                r_->hcount.store(1, std::memory_order_seq_cst);
                r_->avail.store(NIL, std::memory_order_seq_cst);
            }
            // Reader (RPC process): attach the EXISTING segment (exec created it;
            // no create, no unlink). r_ stays null on failure (e.g. exec not up).
            bool open(char const *const name)
            {
                fd_ = ::shm_open(name, O_RDWR, 0600);
                if (fd_ == -1) {
                    return false;
                }
                void *const m = ::mmap(
                    nullptr, sizeof(Region), PROT_READ | PROT_WRITE, MAP_SHARED,
                    fd_, 0);
                if (m == MAP_FAILED) {
                    ::close(fd_);
                    fd_ = -1;
                    return false;
                }
                r_ = static_cast<Region *>(m);
                return true;
            }
            void close()
            {
                if (r_ != nullptr) {
                    ::munmap(r_, sizeof(Region));
                    r_ = nullptr;
                }
                if (fd_ != -1) {
                    ::close(fd_);
                    fd_ = -1;
                }
            }

            // Exec: the refs currently protected (nonzero HP1/HP2 over [1, hcount)).
            void collect(std::unordered_set<uint64_t> &out) const
            {
                uint32_t const n = r_->hcount.load(std::memory_order_seq_cst);
                for (uint32_t i = 1; i < n; ++i) {
                    uint64_t const a =
                        r_->entries[i].hp1.load(std::memory_order_seq_cst);
                    uint64_t const b =
                        r_->entries[i].hp2.load(std::memory_order_seq_cst);
                    if (a != 0) {
                        out.insert(a);
                    }
                    if (b != 0) {
                        out.insert(b);
                    }
                }
            }

            // Reader side (mm_hp lock-bit pool). Unused until RPC is wired; the
            // self-test exercises it. acquire pops the free list (a pop-lock in the
            // head bit avoids ABA among multiple readers) else bumps hcount.
            uint32_t acquire()
            {
                for (;;) {
                    uint32_t a = r_->avail.load(std::memory_order_seq_cst);
                    if (a & LOCK) {
                        continue; // another popper holds the lock
                    }
                    if (a == NIL) {
                        uint32_t const i =
                            r_->hcount.fetch_add(1, std::memory_order_seq_cst);
                        MONAD_ASSERT(i < MAX);
                        return i;
                    }
                    if (r_->avail.compare_exchange_weak(
                            a, a | LOCK, std::memory_order_seq_cst)) {
                        uint32_t const idx = a; // lock clear in a => the head index
                        uint32_t const next = r_->entries[idx].avail_next.load(
                            std::memory_order_seq_cst);
                        r_->avail.store(next, std::memory_order_seq_cst); // pop+unlock
                        r_->entries[idx].avail_next.store(
                            NIL, std::memory_order_seq_cst);
                        return idx;
                    }
                }
            }
            void publish1(uint32_t const i, uint64_t const ref)
            {
                r_->entries[i].hp1.store(ref, std::memory_order_seq_cst);
            }
            void publish2(uint32_t const i, uint64_t const ref)
            {
                r_->entries[i].hp2.store(ref, std::memory_order_seq_cst);
            }
            // Read back a slot's request-long pin: the block root a handle
            // protects, so a read carries the handle and needs no side map.
            uint64_t peek2(uint32_t const i) const
            {
                return r_->entries[i].hp2.load(std::memory_order_seq_cst);
            }
            void release(uint32_t const i)
            {
                r_->entries[i].hp1.store(0, std::memory_order_seq_cst);
                r_->entries[i].hp2.store(0, std::memory_order_seq_cst);
                for (;;) {
                    uint32_t a = r_->avail.load(std::memory_order_seq_cst);
                    if (a & LOCK) {
                        continue; // spin while a popper holds the lock
                    }
                    r_->entries[i].avail_next.store(a, std::memory_order_seq_cst);
                    if (r_->avail.compare_exchange_weak(
                            a, i, std::memory_order_seq_cst)) {
                        return;
                    }
                }
            }
        };


        // Resolve a ref without I/O: a cache hit; else nullptr (device miss).
        inline unsigned char const *resolve_sync(Ctx const &c, uint64_t const ref)
        {
            NodeCache::ConstAccessor acc;
            if (c.kvio->cache->find(acc, ref)) {
                return acc->second->val.data();
            }
            return nullptr;
        }

        // Internal-node child selection (mirrors descend_to_leaf): last
        // separator <= key, clamped to child 0 for a key below sep_0.
        inline uint64_t pick_child(unsigned char const *const n,
            unsigned char const *const key)
        {
            size_t const kl = n[1];
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            unsigned char const *const p = n + HDR;
            size_t const esz = kl + 8;
            long chosen = -1;
            for (size_t i = 0; i < count; ++i) {
                if (std::memcmp(p + i * esz, key, kl) <= 0) {
                    chosen = static_cast<long>(i);
                }
                else {
                    break;
                }
            }
            if (chosen < 0) {
                chosen = 0;
            }
            uint64_t ref;
            std::memcpy(
                &ref, p + static_cast<size_t>(chosen) * esz + kl, sizeof(ref));
            return ref;
        }

        // Fetch one node: cache hit -> fire `cont` synchronously; else submit an
        // async read to KvIo (its completion caches the node and fires `cont`).
        // The caller drains KvIo to run the descent to completion.
        inline void kv_read_node(Ctx c, uint64_t const ref, NodeCont cont)
        {
            if (unsigned char const *const n = resolve_sync(c, ref);
                n != nullptr) {
                cont(n, /*was_device_read=*/false); // cache / RAM-buffer hit
                return;
            }
            c.kvio->submit_read(ref, std::move(cont));
        }

        // Descend from `ref` to the leaf whose range contains `key`, then call
        // `on_leaf(leaf, depth, io)`. `depth` counts nodes on this descent
        // (root = 1) and `io` how many were device reads; the caller starts them
        // higher to continue a prior descent (a storage subtree continues its
        // account descent), so on_leaf gets the per-lookup totals.
        inline void kv_to_leaf(
            Ctx c, uint64_t const ref, KeyBuf const key, LeafCont on_leaf,
            uint32_t const depth = 1, uint32_t const io = 0)
        {
            kv_read_node(
                c, ref,
                [c, key, on_leaf = std::move(on_leaf), depth, io](
                    unsigned char const *const n, bool const was_io) mutable {
                    uint32_t const cur_io = io + (was_io ? 1u : 0u);
                    // N_BLOCK_ROOT descends like N_INTERNAL (entries at HDR).
                    if (n[0] != N_INTERNAL && n[0] != N_BLOCK_ROOT) {
                        on_leaf(n, depth, cur_io);
                        return;
                    }
                    kv_to_leaf(
                        c,
                        pick_child(n, key.data()),
                        key,
                        std::move(on_leaf),
                        depth + 1,
                        cur_io);
                });
        }
    }
}

// Loaded KV image + shadow-comparison counters (definition matches the
// forward declaration in trie_db.hpp).
struct KvShadow
{
    uint64_t image_bytes{0};
    kv::KvHeader hdr{};
    // Current KV root — starts at the image root, advances as blocks commit.
    // New nodes are built in the RAM write buffer (wbuf_), then written to their
    // assigned refs; the device base image is read-only. (Base + committed nodes
    // are on-device; no mmap — reads go through io_uring/pread.)
    uint64_t root_{0};
    std::atomic<uint64_t> acc_checked{0};
    std::atomic<uint64_t> acc_mismatch{0};
    std::atomic<uint64_t> sto_checked{0};
    std::atomic<uint64_t> sto_mismatch{0};
    // kvdb_base multiversion: historical-read validation counters (KV read at a
    // past block's ring root vs triedb at that version).
    std::atomic<uint64_t> mv_acc_checked{0};
    std::atomic<uint64_t> mv_acc_mismatch{0};
    std::atomic<uint64_t> mv_sto_checked{0};
    std::atomic<uint64_t> mv_sto_mismatch{0};
    std::atomic<uint64_t> mv_skipped{0}; // block predates the KV or triedb window
    // Undecided-proposal validation: KV tip (root_) vs triedb proposal subtrie.
    std::atomic<uint64_t> up_acc_checked{0};
    std::atomic<uint64_t> up_acc_mismatch{0};
    std::atomic<uint64_t> up_sto_checked{0};
    std::atomic<uint64_t> up_sto_mismatch{0};
    // RPC read-side validation (KVDB_RDTEST): a KvReader opened on the live
    // store -- the same path the RPC process takes -- reading the finalized tip
    // under a hazard-protected handle, compared against triedb at that version.
    // rd_pins counts successful protect_block calls; rd_pin_fail a tip that the
    // reader could not pin (should stay 0 for a finalized, retained block).
    std::atomic<uint64_t> rd_pins{0};
    std::atomic<uint64_t> rd_pin_fail{0};
    std::atomic<uint64_t> rd_acc_checked{0};
    std::atomic<uint64_t> rd_acc_mismatch{0};
    std::atomic<uint64_t> rd_sto_checked{0};
    std::atomic<uint64_t> rd_sto_mismatch{0};
    std::atomic<uint64_t> rd_code_checked{0};
    std::atomic<uint64_t> rd_code_mismatch{0};
    // Blob + index round trips: read the block's header blob and resolve
    // keccak(header) through the block-hash index back to this block number;
    // read its tx-hash blob and resolve the first hash back to (block, 0).
    std::atomic<uint64_t> rd_blob_checked{0};
    std::atomic<uint64_t> rd_blob_mismatch{0};
    std::atomic<uint64_t> rd_index_checked{0};
    std::atomic<uint64_t> rd_index_mismatch{0};
    // Held-pin snapshot stability (KVDB_RDHOLD): reads through a handle kept
    // across commits, while prune advances past its block.
    std::atomic<uint64_t> rd_hold_checked{0};
    std::atomic<uint64_t> rd_hold_mismatch{0};
    std::atomic<uint64_t> rd_hold_blocks{0}; // commits the pin was held across
    // Per-tx table categories (receipts / transactions / call frames): entry
    // count vs the block's tx count, and each tx's blob non-empty.
    std::atomic<uint64_t> rd_tx_checked{0};
    std::atomic<uint64_t> rd_tx_mismatch{0};
    // protect_block's failure path: pinning a block below the retained window
    // must return -1. Counted separately from rd_pin_fail (which is a bug).
    std::atomic<uint64_t> rd_pruned_checked{0};
    std::atomic<uint64_t> rd_pruned_mismatch{0};
    // Pinning an UNDECIDED block by its proposal id: state read through that
    // pin vs triedb's proposal subtrie, plus a perturbed id that must NOT pin
    // (a height can carry several proposals, so an id-blind pin could return a
    // sibling's root and still look like it worked).
    std::atomic<uint64_t> rd_prop_checked{0};
    std::atomic<uint64_t> rd_prop_mismatch{0};
    // Tag-cursor snapshot: the reader's (block, id) pairs vs triedb's own
    // cursors. rd_tag_retries is the bracket's re-read count; zero means the
    // race did not occur in this run, not that the retry is correct.
    std::atomic<uint64_t> rd_tag_checked{0};
    std::atomic<uint64_t> rd_tag_mismatch{0};
    std::atomic<uint64_t> rd_tag_retries{0};

    // Sibling-fork structural counters (KVDB_SIBLING_EVERY test). fork_commits:
    // a proposal was committed onto a parent that already had a child at that
    // height (a real fork formed). fork_finalized: finalize rerooted a node that
    // had >1 child (finalize discriminated between siblings). Both are printed
    // at exit; if the knob is on and they are zero, the test did nothing.
    std::atomic<uint64_t> fork_commits{0};
    std::atomic<uint64_t> fork_finalized{0};

    // Code-read shadow validation: KV code vs triedb code.
    std::atomic<uint64_t> code_checked{0};
    std::atomic<uint64_t> code_mismatch{0};
    // Parallel-fetch tracking: code reads that pulled >1 data page, and the
    // total data pages fetched in parallel (device-read misses) across them.
    std::atomic<uint64_t> code_multipage_reads{0};
    std::atomic<uint64_t> code_parallel_io{0};

    // ── device I/O state (kvdb_base separation) ─────────────────────────
    // LRU over raw 4KB device nodes. KV owns a flat page array on its OWN fd,
    // independent of triedb's storage_pool: node_ref maps to the absolute device
    // offset kv_base_ + ref (no chunks). kv_base_ = phys(seq chunk
    // KVDB_FIRST_SEQ_CHUNK), read from the .kvhdr (KvHeader::base_offset) the
    // builder recorded; triedb's allocation guard keeps it out of [kv_base_,end).
    static constexpr size_t KV_CACHE_ENTRIES = 1u << 16; // 65536 x 4KB = 256MiB
    kv::NodeCache cache_{KV_CACHE_ENTRIES};
    int kv_fd_{-1};
    uint64_t kv_base_{0};
    // KV's own async io_uring engine (O_DIRECT, registered buffers). Lazily
    // built on the DB io thread on first use (the ring must be created and
    // driven on the thread that owns it).
    std::unique_ptr<kv::KvIo> kvio_;

    // Commit write state. New nodes are built into `wbuf_` (per-block RAM
    // scratch); each is assigned a page ref by allocate_page (a bump or a reused
    // reclaimed page, so refs are NOT contiguous). `wref_[i]` is wbuf_[i]'s ref
    // (used by the device write pass); `wbuf_index_` maps ref -> wbuf_ index so a
    // commit read finds a node built this block by ref. All three cleared per
    // block.
    std::vector<std::array<unsigned char, kv::NODE_SIZE>> wbuf_;
    std::vector<uint64_t> wref_;
    std::unordered_map<uint64_t, uint32_t> wbuf_index_;
    uint64_t write_pos_{0}; // next ref for a bump (past the reused region)
    uint64_t blocks_committed_{0}; // kvdb_base: for append-growth measurement
    uint64_t kv_commit_us_{0}; // last block's KV commit latency (kv_cmt phase)

    // ── reclamation step 1: per-page slot array + lock-free freelist ──────
    // One 4B slot per page over the FULL KV page region (every page we can ever
    // bump). Each slot is a tagged union by its top bit (SLOT_FREE_BIT):
    //   live page  (bit 0): the node's link count       (step 2 semantics)
    //   free page  (bit 1): serial of the next free page (this freelist)
    // The two uses never overlap in time (a page is live xor free). The freelist
    // is the classic IBM lock-free freelist: a single atomic head holding a page
    // serial (SLOT_NIL == empty), pop via CAS, push via CAS, next-links kept in
    // the slot array. SINGLE-POPPER INVARIANT: only the exec io thread calls
    // allocate_page(); the (future) reclaim thread only calls free_page(). One
    // popper => no ABA => no pop-lock / no version tag. Adding a second allocator
    // thread reintroduces ABA and requires a pop-lock (low bit of the head).
    // In step 1 nothing pushes, so the list stays empty and allocate_page always
    // bumps: behavior is identical to the pre-reclamation bump allocator.
    static constexpr uint32_t SLOT_FREE_BIT = 0x80000000u;
    static constexpr uint32_t SLOT_PAYLOAD = 0x7FFFFFFFu;
    // "No page" sentinel: the empty-list head AND a free slot's end-of-chain
    // next-link. Must fit in SLOT_PAYLOAD (a slot's next-link is only 31 bits),
    // so it is the max payload value, which is not a real serial (2^31 pages =
    // 8TB, far past any device). 0xFFFFFFFF would read back as 0x7FFFFFFF after
    // masking and break chain termination.
    static constexpr uint32_t SLOT_NIL = SLOT_PAYLOAD;
    std::vector<std::atomic<uint32_t>> pageslot_; // indexed by page serial
    std::atomic<uint32_t> freelist_head_{SLOT_NIL};
    uint64_t max_pages_{0}; // size of pageslot_ (full region page count)

    // Roots retired but not yet released (their release cascade is deferred until
    // no hazard pointer names them). A block-map root is retired each time it is
    // superseded; a state root is retired when its block leaves the window (or a
    // sibling proposal loses). The reclaim step drains this, hazard-gated.
    // Single producer (commit/finalize) today; becomes a concurrent queue when a
    // background reclaim thread is added.
    struct RetiredRoot
    {
        uint64_t ref;
        bool is_state_root; // true => gated by a state-root hazard, else block-map
    };
    std::vector<RetiredRoot> retired_roots_;

    // Reclamation counters (single exec thread today; plain). freed = pages
    // pushed to the freelist; reused = allocate pops that reused a freed page;
    // reclaimed_roots = retired roots released.
    uint64_t freed_pages_{0};
    uint64_t reused_pages_{0};
    uint64_t reclaimed_roots_{0};
    // Times reclaim skipped a retired root because a reader's hazard named it.
    uint64_t hz_deferred_{0};
    // Run the reclaim step every N finalizes (env KVDB_RECLAIM_EVERY, default 1).
    uint64_t reclaim_every_{1};
    // Cap on roots released per reclaim call (bounds latency; leftovers wait).
    static constexpr uint64_t RECLAIM_BATCH = 4096;
    // Per-block reclaim stat line (env KVDB_RECLAIM_LOG=1). Deltas since last
    // block; `bump` going to 0 marks the storage plateau.
    bool reclaim_log_{false};
    uint64_t prev_bumped_{0};
    uint64_t prev_reused_{0};
    uint64_t prev_freed_{0};

    // Shared-memory HP array. Struct lifted to kv:: (see the kv namespace) so
    // the RPC read side reuses it. Exec creates + scans; the reader attaches.
    kv::HazardArray haz_;

    void retire_root(uint64_t const ref, bool const is_state_root)
    {
        retired_roots_.push_back({ref, is_state_root});
    }

    // Swap in a new block-map root: the metadata pointer is its one reference, so
    // add a link; the superseded old root is retired (released later, once no
    // hazard names it). The single place block-map roots change (commit insert,
    // finalize unlink, prune).
    void install_block_map_root(uint64_t const new_root)
    {
        uint64_t const old = meta_->tree_root;
        link_inc(new_root);
        // seq_cst publish: the cross-process RPC reader loads tree_root seq_cst
        // and pins it (HP1) before walking, so a superseded root it is reading is
        // still in the retired list (hazard-gated) when reclaim scans. Exec is the
        // only writer, so its own plain reads of tree_root elsewhere are fine.
        __atomic_store_n(&meta_->tree_root, new_root, __ATOMIC_SEQ_CST);
        if (old != new_root && old != kv::NULL_REF) {
            retire_root(old, /*is_state_root=*/false);
        }
    }

    // Same, for a hash-index root (tx-hash / block-hash). Called once per COW
    // insert/unlink; the superseded root is retired hazard-gated (readers walk
    // the index under a transient hazard, so a still-referenced old root waits).
    void install_index_root(uint64_t &root_field, uint64_t const new_root)
    {
        uint64_t const old = root_field;
        link_inc(new_root);
        // seq_cst publish, as for tree_root: the RPC reader resolves a hash under
        // a transient hazard (pin the root, re-load to confirm it is current, walk),
        // which needs this store ordered against its pin.
        __atomic_store_n(&root_field, new_root, __ATOMIC_SEQ_CST);
        if (old != new_root && old != kv::NULL_REF) {
            retire_root(old, /*is_state_root=*/false);
        }
    }
    // Hash index key/value sizes (blockmap B+tree).
    static constexpr size_t TXH_KL = 32, TXH_VL = 12; // hash -> (block8, idx4)
    static constexpr size_t BLKH_KL = 32, BLKH_VL = 8; // hash -> number8

    // Read mode: true => triedb serves and KV reads are compared (testing);
    // false (env KVDB_SHADOW=0) => KV serves reads, no triedb read/compare
    // (perf). Commit always writes KV either way.
    bool shadow_{true};

    // kvdb_base multiversion: the on-device metadata block, mmap'd RW. Holds the
    // block map root, the finalized frontier, and the oldest retained block.
    void *meta_map_{nullptr};
    kv::KvMeta *meta_{nullptr};
    // Read cursor (in-memory): the parent id set by set_tip, stored in the block
    // map entry for the child committed next. root_ holds the parent's state
    // root (the base the next commit builds on).
    bytes32_t cur_parent_id_{};

    kv::KvIo &kvio()
    {
        if (!kvio_) {
            kvio_ = std::make_unique<kv::KvIo>(kv_fd_, kv_base_, &cache_);
        }
        return *kvio_;
    }

    // Null until the first KV io (which lazily creates the engine on the io
    // thread). Read by the io-loop poll hook to reap the KV ring.
    kv::KvIo *kvio_ptr() { return kvio_.get(); }

    kv::Ctx read_ctx(MONAD_ASYNC_NAMESPACE::AsyncIO & /*io*/)
    {
        return kv::Ctx{&kvio()};
    }

    // `path` is the KV header (.kvhdr) sidecar; the node data lives on-device.
    explicit KvShadow(char const *const path)
    {
        int const sfd = ::open(path, O_RDONLY);
        MONAD_ASSERT(sfd != -1);
        ssize_t const r = ::read(sfd, &hdr, sizeof(hdr));
        MONAD_ASSERT(r == static_cast<ssize_t>(sizeof(hdr)));
        ::close(sfd);
        MONAD_ASSERT(hdr.magic == kv::MAGIC);
        MONAD_ASSERT(hdr.node_size == kv::NODE_SIZE);
        image_bytes = hdr.image_bytes;
        root_ = hdr.root_ref;
        kv_base_ = hdr.base_offset;
        // KV's own fd to the backing device: a flat array of 4KB pages at
        // kv_base_ + ref, independent of triedb's storage_pool. O_DIRECT: the KV
        // io engine (KvIo, io_uring + registered buffers) and the commit-path
        // NodeReader's rare pread both use aligned 4KB buffers. Device path from
        // $KVDB_DEVICE (default /dev/triedb), matching the $KVDB_IMAGE pattern.
        char const *const dev = std::getenv("KVDB_DEVICE");
        // Buffered by default (KV reads/writes go through the OS page cache, so
        // a node evicted from the in-memory NodeCache but still page-cache-warm
        // is served without a device round-trip). $KVDB_ODIRECT=1 forces
        // O_DIRECT (bypass page cache) to compare.
        int oflags = O_RDWR;
        if (char const *const od = std::getenv("KVDB_ODIRECT");
            od != nullptr && std::strcmp(od, "1") == 0) {
            oflags |= O_DIRECT;
        }
        kv_fd_ = ::open(dev != nullptr ? dev : "/dev/triedb", oflags);
        MONAD_ASSERT(kv_fd_ != -1);
        // Reclamation step 1: allocate the per-page slot array over KV's whole
        // page region [kv_base_, device_end) = every page allocate_page could
        // ever bump. SEEK_END on a block device returns its byte size.
        {
            off_t const end = ::lseek(kv_fd_, 0, SEEK_END);
            MONAD_ASSERT(end != -1);
            MONAD_ASSERT(static_cast<uint64_t>(end) > kv_base_);
            max_pages_ =
                (static_cast<uint64_t>(end) - kv_base_) / kv::NODE_SIZE;
            MONAD_ASSERT(max_pages_ < SLOT_NIL); // serials must not hit sentinel
            pageslot_ = std::vector<std::atomic<uint32_t>>(max_pages_);
            // Link-count init: every image node has exactly one reference (its
            // parent link; the block-map root's is the metadata pointer), so
            // set count 1 across the image's pages. Nodes live in
            // [KVDB_META_BYTES, image_bytes); the metadata region below it is
            // in-place, not link-counted. Pages past the image start at 0 and
            // are set by allocate_page.
            for (uint64_t r = KVDB_META_BYTES; r < image_bytes;
                 r += kv::NODE_SIZE) {
                pageslot_[r / kv::NODE_SIZE].store(
                    1, std::memory_order_relaxed);
            }
        }
        if (char const *const s = std::getenv("KVDB_SHADOW");
            s != nullptr && std::strcmp(s, "0") == 0) {
            shadow_ = false;
        }
        // Reclaim cadence: run the reclaim step every N finalizes (default 1).
        if (char const *const s = std::getenv("KVDB_RECLAIM_EVERY")) {
            reclaim_every_ = std::strtoull(s, nullptr, 10);
        }
        if (char const *const s = std::getenv("KVDB_RECLAIM_LOG");
            s != nullptr && std::strcmp(s, "1") == 0) {
            reclaim_log_ = true;
        }
        // Hazard-pointer array (shared memory). Exec creates + scans it; the RPC
        // reader (not built) will publish into the same segment.
        haz_.create("/kvdb_hazards");
        // kvdb_base multiversion: mmap the on-device metadata region (front of
        // KV's range) RW. mmap goes through the page cache regardless of the
        // node fd's O_DIRECT mode; the region is tiny and off the read hot path.
        // kv_base_ is 4KB-aligned (phys of a seq chunk, or 0 for a file).
        {
            void *const m = ::mmap(
                nullptr,
                KVDB_META_BYTES,
                PROT_READ | PROT_WRITE,
                MAP_SHARED,
                kv_fd_,
                static_cast<off_t>(kv_base_));
            MONAD_ASSERT(m != MAP_FAILED);
            meta_map_ = m;
            meta_ = static_cast<kv::KvMeta *>(m);
            MONAD_ASSERT(meta_->magic == kv::META_MAGIC);
            MONAD_ASSERT(meta_->version == 7);
            MONAD_ASSERT(meta_->node_size == kv::NODE_SIZE);
        }
        // The read cursor is positioned by set_tip before the first commit.
    }

    ~KvShadow()
    {
        if (meta_map_ != nullptr) {
            // Reclamation totals: bumped = pages ever bump-allocated (region high
            // water), reused = allocations served from the freelist, freed =
            // pages returned by the reclaim step, retired left = roots awaiting
            // release (hazard-held or capped). If reuse keeps pace, `bumped`
            // plateaus while `reused` grows.
            uint64_t const bumped = write_pos_ >= image_bytes
                                        ? (write_pos_ - image_bytes) /
                                              kv::NODE_SIZE
                                        : 0;
            std::fprintf(
                stderr,
                "KVDB_PROTO reclaim totals: reclaimed_roots=%llu freed_pages=%llu "
                "reused_pages=%llu bumped_pages=%llu retired_left=%zu "
                "hz_deferred=%llu\n",
                static_cast<unsigned long long>(reclaimed_roots_),
                static_cast<unsigned long long>(freed_pages_),
                static_cast<unsigned long long>(reused_pages_),
                static_cast<unsigned long long>(bumped),
                retired_roots_.size(),
                static_cast<unsigned long long>(hz_deferred_));
            if (char const *const s = std::getenv("KVDB_LCCHECK");
                s != nullptr && std::strcmp(s, "1") == 0) {
                lc_check();
            }
            ::msync(meta_map_, KVDB_META_BYTES, MS_SYNC);
            ::munmap(meta_map_, KVDB_META_BYTES);
            meta_map_ = nullptr;
        }
        haz_.close();
    }

    // Commit-time resolver: this block's write buffer for new nodes, else
    // cache/pread on kv_fd_ for committed nodes. Valid only during a commit
    // (wbuf_/wbuf_index_ are populated on the io thread by commit_block).
    kv::NodeReader node_reader()
    {
        return kv::NodeReader{&wbuf_, &wbuf_index_, &cache_, kv_fd_, kv_base_};
    }

    // Allocate one page, returning its byte ref (offset from kv_base_). Pops the
    // freelist if non-empty, else bumps write_pos_. THE ONLY allocation
    // chokepoint. Single-popper: called only on the exec io thread (see the
    // freelist member comment) => plain CAS loop, no ABA, no pop-lock.
    uint64_t allocate_page()
    {
        uint32_t h = freelist_head_.load(std::memory_order_acquire);
        while (h != SLOT_NIL) {
            // Free slot holds the next free serial; only the pusher writes it,
            // and our acquire-load of the head synchronizes with that release.
            uint32_t const next =
                pageslot_[h].load(std::memory_order_relaxed) & SLOT_PAYLOAD;
            if (freelist_head_.compare_exchange_weak(
                    h, next, std::memory_order_acquire)) {
                // Reused page starts with 0 links; its links are added as
                // parents point to it (inc_children at each parent's emit).
                pageslot_[h].store(0, std::memory_order_relaxed);
                ++reused_pages_;
                return static_cast<uint64_t>(h) * kv::NODE_SIZE;
            }
        }
        uint64_t const ref = write_pos_;
        write_pos_ += kv::NODE_SIZE;
        uint32_t const s = static_cast<uint32_t>(ref / kv::NODE_SIZE);
        MONAD_ASSERT(s < max_pages_);
        pageslot_[s].store(0, std::memory_order_relaxed); // 0 links yet
        return ref;
    }

    // Return a page to the freelist (push). Called only by the (future) reclaim
    // thread; uncalled in step 1, so the list stays empty and every
    // allocate_page bumps. Lock-free push: write next-link into the slot, then
    // CAS the head; races only with allocate_page's pop and other pushes.
    void free_page(uint64_t const ref)
    {
        uint32_t const s = static_cast<uint32_t>(ref / kv::NODE_SIZE);
        MONAD_ASSERT(s < max_pages_);
        uint32_t h = freelist_head_.load(std::memory_order_relaxed);
        do {
            pageslot_[s].store(SLOT_FREE_BIT | h, std::memory_order_relaxed);
        }
        while (!freelist_head_.compare_exchange_weak(
            h, s, std::memory_order_release, std::memory_order_relaxed));
    }

    // ── reclamation step 2: link counts ─────────────────────────────────
    // A node->child reference falls into one of:
    //   Node      - an ordinary reclaimable node (counted; freed + recursed).
    //   Terminal  - a raw page with no header (a storage out-of-line value page):
    //               counted and freed, but NEVER walked as a node.
    //   StateRoot - a block-map leaf's state_root. NOT counted as a link and the
    //               block-map cascade never touches it: a state root's count is a
    //               single "present in block map" link, added at commit and
    //               removed at prune (then it is retired, HP2-reclaimed).
    enum class ChildKind
    {
        Node,
        Terminal,
        StateRoot
    };

    // Call fn(child_ref, kind) for every node->child reference this node holds
    // (skipping NULL_REF). THE one place that knows per-type child layout. Code
    // nodes (N_CODE_*) and value-only storage leaves (N_LEAF_STORAGE_FLAT) hold
    // no reclaimable child refs.
    template <class F>
    static void for_each_child_ref(unsigned char const *const n, F &&fn)
    {
        auto yield = [&fn](uint64_t const r, ChildKind const k) {
            if (r != kv::NULL_REF) {
                fn(r, k);
            }
        };
        switch (n[0]) {
        case kv::N_BLOCK_ROOT:
        case kv::N_INTERNAL: {
            size_t const kl = n[1];
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            unsigned char const *const p = n + kv::HDR;
            for (size_t i = 0; i < count; ++i) {
                uint64_t r;
                std::memcpy(&r, p + i * (kl + 8) + kl, 8);
                yield(r, ChildKind::Node);
            }
            // A block root additionally owns its per-block blob roots (tail),
            // as ordinary link-counted Node children reclaimed with it.
            if (n[0] == kv::N_BLOCK_ROOT) {
                for (size_t b = 0; b < kv::BLOB_N; ++b) {
                    uint64_t r;
                    std::memcpy(
                        &r, n + kv::BLOCK_ROOT_BLOB_OFF + b * 8, 8);
                    yield(r, ChildKind::Node);
                }
            }
            break;
        }
        case kv::N_LEAF_ACCOUNT: {
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            unsigned char const *const p = n + kv::HDR;
            for (size_t i = 0; i < count; ++i) {
                uint64_t sref; // storage-root ref: last 8B of the record
                std::memcpy(
                    &sref, p + i * kv::ACCT_REC + 20 + sizeof(Account), 8);
                yield(sref, ChildKind::Node);
            }
            break;
        }
        case kv::N_BLOB_INDEX: {
            // Height 0 (n[1]): children are raw data pages, which must NOT be
            // parsed as nodes. Above that they are index pages of the level
            // below, so they are ordinary link-counted nodes and the free
            // cascades through them.
            bool const leaf = n[1] == 0;
            uint32_t nc;
            std::memcpy(&nc, n + 16 /*CODE_NCHILD*/, sizeof(nc));
            for (size_t i = 0; i < nc; ++i) {
                uint64_t r;
                std::memcpy(&r, n + 24 /*CODE_CHILDREN*/ + i * 8, 8);
                yield(r, leaf ? ChildKind::Terminal : ChildKind::Node);
            }
            break;
        }
        case kv::N_BLOB_TABLE: {
            // Children are blob roots at height 0 (n[1]) and child tables above
            // it -- nodes either way. The child count is the entry count only
            // at height 0; above that it has its own field.
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            size_t nchild = count; // height 0: one child per entry
            if (n[1] != 0) {
                uint32_t span;
                std::memcpy(&span, n + 4, sizeof(span));
                MONAD_ASSERT(span != 0);
                nchild = (count + span - 1) / span;
            }
            for (size_t i = 0; i < nchild; ++i) {
                uint64_t r;
                std::memcpy(&r, n + kv::HDR + i * 8, 8);
                yield(r, ChildKind::Node);
            }
            break;
        }
        case kv::N_LEAF_STORAGE_PAGE: {
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            unsigned char const *const p = n + kv::HDR;
            for (size_t i = 0; i < count; ++i) {
                uint16_t off;
                std::memcpy(&off, p + i * 2, sizeof(off));
                unsigned char const *const rec = n + off;
                if (rec[kv::PG_FLAG] != 0) { // out-of-line raw value page
                    uint64_t ext;
                    std::memcpy(&ext, rec + kv::PG_PAYLOAD, 8);
                    yield(ext, ChildKind::Terminal);
                }
            }
            break;
        }
        case kv::N_BLOCKMAP_INTERNAL: {
            uint16_t nc;
            std::memcpy(&nc, n + kv::blockmap::BP_COUNT, sizeof(nc));
            for (size_t i = 0; i < nc; ++i) {
                yield(kv::blockmap::child_ref(n, i), ChildKind::Node);
            }
            break;
        }
        case kv::N_BLOCKMAP_LEAF: {
            size_t const kl = n[kv::blockmap::BP_KEYLEN];
            size_t const vl = n[kv::blockmap::BP_VALLEN];
            uint16_t count;
            std::memcpy(&count, n + kv::blockmap::BP_COUNT, sizeof(count));
            for (size_t i = 0; i < count; ++i) {
                uint64_t br; // block_root: first 8B of the value
                std::memcpy(&br, kv::blockmap::leaf_val(n, i, kl, vl), 8);
                yield(br, ChildKind::StateRoot);
            }
            break;
        }
        default:
            break; // storage-flat leaf, code nodes: no reclaimable refs
        }
    }

    // Add one link to page `ref` (a parent now points to it).
    void link_inc(uint64_t const ref)
    {
        uint32_t const s = static_cast<uint32_t>(ref / kv::NODE_SIZE);
        MONAD_ASSERT(s < max_pages_);
        pageslot_[s].fetch_add(1, std::memory_order_relaxed);
    }

    // A node was just emitted: add one link to each of its children. New
    // children were reset to 0 by allocate_page and reach 1 here; reused old
    // children rise above their prior count. No old/new distinction needed.
    void inc_children(unsigned char const *const buf)
    {
        for_each_child_ref(
            buf, [this](uint64_t const c, ChildKind const k) {
                // State roots are not counted per block-map leaf; their single
                // "present" link is added explicitly at commit.
                if (k != ChildKind::StateRoot) {
                    link_inc(c);
                }
            });
    }

    // Remove one link to `ref`; when the last link goes, free the page and
    // release each of its children (recurse). `terminal` pages are raw (no
    // header): freed directly, never read. Shared by production release_page and
    // the self-test via an injected `read_into(ref, dst)` (device pread vs an
    // in-memory map). free-at-0 needs no CAS: a count-1 page has one parent, so
    // only one releaser can observe 0. The decrement is the racy step and uses
    // CAS so the last releaser is the one that frees.
    // Returns the number of pages freed (this page plus its cascade).
    template <class ReadInto>
    static uint64_t gen_release(
        std::vector<std::atomic<uint32_t>> &slots, std::atomic<uint32_t> &head,
        ReadInto read_into, uint64_t const ref, ChildKind const kind)
    {
        // A block-map cascade never touches a state root: its count is the single
        // "present" link, released only at prune (which retires it separately).
        if (kind == ChildKind::StateRoot) {
            return 0;
        }
        uint32_t const s = static_cast<uint32_t>(ref / kv::NODE_SIZE);
        uint32_t v = slots[s].load(std::memory_order_acquire);
        for (;;) {
            MONAD_ASSERT(!(v & SLOT_FREE_BIT)); // not already free
            MONAD_ASSERT(v != 0); // releasing a page with no links is a bug
            if (v == 1) {
                break; // removing the last link -> free below
            }
            if (slots[s].compare_exchange_weak(
                    v, v - 1, std::memory_order_acq_rel)) {
                return 0; // still referenced by another parent
            }
        }
        // Last link. Push the page onto the freelist (its slot becomes the
        // next-free link). For a terminal raw page there is nothing to recurse
        // into.
        uint32_t h = head.load(std::memory_order_relaxed);
        do {
            slots[s].store(SLOT_FREE_BIT | h, std::memory_order_relaxed);
        }
        while (!head.compare_exchange_weak(
            h, s, std::memory_order_release, std::memory_order_relaxed));
        if (kind == ChildKind::Terminal) {
            return 1;
        }
        // Snapshot children before recursing (read_into may reuse its buffer),
        // then release each.
        std::array<unsigned char, kv::NODE_SIZE> buf;
        read_into(ref, buf.data());
        std::vector<std::pair<uint64_t, ChildKind>> kids;
        for_each_child_ref(
            buf.data(), [&kids](uint64_t const c, ChildKind const k) {
                kids.emplace_back(c, k);
            });
        uint64_t freed = 1;
        for (auto const &[c, k] : kids) {
            freed += gen_release(slots, head, read_into, c, k);
        }
        return freed;
    }

    // Read a committed node's 4KB bytes from the device (for the release cascade).
    void read_node_bytes(uint64_t const ref, unsigned char *const dst)
    {
        ssize_t const n = ::pread(
            kv_fd_, dst, kv::NODE_SIZE, static_cast<off_t>(kv_base_ + ref));
        MONAD_ASSERT(n == static_cast<ssize_t>(kv::NODE_SIZE));
    }

    // Release one link to `ref` (a root reference or a parent link going away),
    // freeing dead pages. `kind` is ChildKind::Node for a root. Returns pages
    // freed.
    uint64_t release_page(uint64_t const ref, ChildKind const kind)
    {
        return gen_release(
            pageslot_, freelist_head_,
            [this](uint64_t const r, unsigned char *const dst) {
                read_node_bytes(r, dst);
            },
            ref, kind);
    }

    // Retire a state root: drop its single "present in block map" link (must be
    // exactly 1). The page is now unreferenced but is NOT freed — a reader may
    // still hold it (HP2), so it is added to the retired list for the
    // hazard-gated reclaim step to free.
    void retire_state_root(uint64_t const sr)
    {
        uint32_t const s = static_cast<uint32_t>(sr / kv::NODE_SIZE);
        MONAD_ASSERT(s < max_pages_);
        uint32_t const prev =
            pageslot_[s].fetch_sub(1, std::memory_order_acq_rel);
        MONAD_ASSERT(prev == 1); // present link is a state root's only link
        retire_root(sr, /*is_state_root=*/true);
    }

    // Free a retired state root (already at count 0) and cascade its state
    // subtree. Snapshot children before freeing the root (its page may be
    // reused). Returns pages freed.
    uint64_t free_retired_state_root(uint64_t const sr)
    {
        uint32_t const s = static_cast<uint32_t>(sr / kv::NODE_SIZE);
        MONAD_ASSERT(!(pageslot_[s].load() & SLOT_FREE_BIT));
        MONAD_ASSERT(pageslot_[s].load() == 0); // retired: no links
        std::array<unsigned char, kv::NODE_SIZE> buf;
        read_node_bytes(sr, buf.data());
        std::vector<std::pair<uint64_t, ChildKind>> kids;
        for_each_child_ref(
            buf.data(), [&kids](uint64_t const c, ChildKind const k) {
                kids.emplace_back(c, k);
            });
        free_page(sr);
        uint64_t freed = 1;
        for (auto const &[c, k] : kids) {
            freed += release_page(c, k); // state children are Node/Terminal
        }
        return freed;
    }

    // The refs currently protected by a hazard pointer (a reader must not have
    // them freed). Scans the shared-memory hazard array. No RPC publisher yet, so
    // the array is empty and nothing is protected.
    std::unordered_set<uint64_t> collect_hazards()
    {
        std::unordered_set<uint64_t> s;
        haz_.collect(s);
        return s;
    }

    // Release retired roots whose ref no hazard names, freeing their dead
    // subtrees. Bounded per call; protected/leftover roots wait for the next
    // call. Runs on the exec thread (single consumer today).
    void reclaim_step()
    {
        if (retired_roots_.empty()) {
            return;
        }
        std::unordered_set<uint64_t> const hazards = collect_hazards();
        std::vector<RetiredRoot> keep;
        uint64_t budget = RECLAIM_BATCH;
        for (auto const &r : retired_roots_) {
            if (budget == 0 || hazards.count(r.ref)) {
                if (hazards.count(r.ref)) {
                    // A reader's hazard names this root: the free is deferred.
                    // Nonzero proves the cross-process gate actually fired.
                    ++hz_deferred_;
                }
                keep.push_back(r); // capped out, or a reader still holds it
                continue;
            }
            freed_pages_ += r.is_state_root ? free_retired_state_root(r.ref)
                                            : release_page(r.ref, ChildKind::Node);
            ++reclaimed_roots_;
            --budget;
        }
        retired_roots_.swap(keep);
    }

    // Append a 4KB node to this block's write buffer; assign it a page ref. The
    // node is written to the device in the commit's write pass. Returns the ref.
    uint64_t emit(unsigned char const *const buf)
    {
        uint64_t const ref = allocate_page();
        uint32_t const idx = static_cast<uint32_t>(wbuf_.size());
        wbuf_.emplace_back();
        std::memcpy(wbuf_.back().data(), buf, kv::NODE_SIZE);
        wref_.push_back(ref);
        wbuf_index_.emplace(ref, idx);
        inc_children(buf);
        return ref;
    }

    // Emit a raw value page (no node type / children): skip inc_children so its
    // arbitrary bytes are never parsed as a node. Its link is taken by the
    // parent index page's inc_children (which yields it as a Terminal child), so
    // it is freed when that parent is freed. Used for N_BLOB_INDEX data pages.
    uint64_t emit_raw(unsigned char const *const buf)
    {
        uint64_t const ref = allocate_page();
        uint32_t const idx = static_cast<uint32_t>(wbuf_.size());
        wbuf_.emplace_back();
        std::memcpy(wbuf_.back().data(), buf, kv::NODE_SIZE);
        wref_.push_back(ref);
        wbuf_index_.emplace(ref, idx);
        return ref;
    }

    // ── item 2: build helpers (build new nodes into the RAM write buffer) ──

    // Balanced split: split `n` entries across ceil(n/cap) nodes of nearly
    // equal size, so no node is a tiny remainder (each holds >= cap/2 when
    // n > cap). Returns the entry count of node `nj`. Greedy [cap,...,remainder]
    // packing shed single-child nodes on every overflow, and split-only merge
    // never reclaimed them, so the tree inflated over time (depth 4 -> 8 over
    // 70K blocks; see debug_raw_260813a). Used by every pack site below.
    static size_t split_count(
        size_t const n, size_t const cap, size_t const nj)
    {
        size_t const k = (n + cap - 1) / cap; // number of nodes (>= 1 for n > 0)
        return n / k + (nj < n % k ? 1 : 0);
    }

    // Pack (key,ref) level entries into internal nodes bottom-up until one
    // root remains; returns its ref (NULL_REF if empty).
    uint64_t pack_internal(std::vector<kv::LevelEnt> ents, size_t const key_len)
    {
        if (ents.empty()) {
            return kv::NULL_REF;
        }
        size_t const esz = key_len + 8;
        size_t const cap = (kv::NODE_SIZE - kv::HDR) / esz;
        while (ents.size() > 1) {
            std::vector<kv::LevelEnt> up;
            size_t const n = ents.size();
            size_t const k = (n + cap - 1) / cap;
            up.reserve(k);
            size_t i = 0;
            for (size_t nj = 0; nj < k; ++nj) {
                size_t const count = split_count(n, cap, nj);
                unsigned char buf[kv::NODE_SIZE];
                std::memset(buf, 0, kv::NODE_SIZE);
                buf[0] = kv::N_INTERNAL;
                buf[1] = static_cast<unsigned char>(key_len);
                uint16_t const c = static_cast<uint16_t>(count);
                std::memcpy(buf + 2, &c, sizeof(c));
                unsigned char *q = buf + kv::HDR;
                for (size_t j = 0; j < count; ++j) {
                    std::memcpy(q, ents[i + j].key, key_len);
                    q += key_len;
                    std::memcpy(q, &ents[i + j].ref, 8);
                    q += 8;
                }
                kv::LevelEnt e;
                std::memcpy(e.key, ents[i].key, key_len);
                e.ref = emit(buf);
                up.push_back(e);
                i += count;
            }
            ents.swap(up);
        }
        return ents[0].ref;
    }

    // Build a flat storage subtree from sorted (slot,value) pairs -> root ref
    // (NULL_REF if empty). Storage leaves emitted flat (reader dispatches per
    // leaf-type, so this mixes fine over a pages base image).
    uint64_t build_storage_flat(
        std::vector<std::pair<bytes32_t, bytes32_t>> const &pairs)
    {
        if (pairs.empty()) {
            return kv::NULL_REF;
        }
        constexpr size_t cap = (kv::NODE_SIZE - kv::HDR) / kv::STOR_REC_FLAT;
        std::vector<kv::LevelEnt> ents;
        size_t const n = pairs.size();
        size_t const k = (n + cap - 1) / cap;
        size_t i = 0;
        for (size_t nj = 0; nj < k; ++nj) {
            size_t const count = split_count(n, cap, nj);
            unsigned char buf[kv::NODE_SIZE];
            std::memset(buf, 0, kv::NODE_SIZE);
            buf[0] = kv::N_LEAF_STORAGE_FLAT;
            buf[1] = static_cast<unsigned char>(kv::STOR_KEY);
            uint16_t const c = static_cast<uint16_t>(count);
            std::memcpy(buf + 2, &c, sizeof(c));
            unsigned char *q = buf + kv::HDR;
            for (size_t j = 0; j < count; ++j) {
                std::memcpy(q, pairs[i + j].first.bytes, 32);
                q += 32;
                std::memcpy(q, pairs[i + j].second.bytes, 32);
                q += 32;
            }
            kv::LevelEnt e;
            std::memcpy(e.key, pairs[i].first.bytes, kv::STOR_KEY);
            e.ref = emit(buf);
            ents.push_back(e);
            i += count;
        }
        return pack_internal(std::move(ents), kv::STOR_KEY);
    }

    // Enumerate a single storage LEAF node's (slot,value) into `m` (handles
    // flat and page formats).
    void enumerate_leaf(
        kv::NodeReader const &R, unsigned char const *const n,
        std::map<
            std::array<unsigned char, 32>, std::array<unsigned char, 32>> &m)
        const
    {
        uint16_t count;
        std::memcpy(&count, n + 2, sizeof(count));
        unsigned char const *p = n + kv::HDR;
        if (n[0] == kv::N_LEAF_STORAGE_FLAT) {
            for (size_t i = 0; i < count; ++i) {
                unsigned char const *rec = p + i * kv::STOR_REC_FLAT;
                std::array<unsigned char, 32> k, v;
                std::memcpy(k.data(), rec, 32);
                std::memcpy(v.data(), rec + 32, 32);
                m[k] = v;
            }
            return;
        }
        MONAD_ASSERT(n[0] == kv::N_LEAF_STORAGE_PAGE);
        for (size_t i = 0; i < count; ++i) {
            uint16_t off;
            std::memcpy(&off, p + i * 2, sizeof(off));
            unsigned char const *rec = n + off;
            std::array<unsigned char, 32> base_key;
            std::memcpy(base_key.data(), rec + kv::PG_BASE, 32);
            unsigned char const *bm = rec + kv::PG_BITMAP;
            unsigned char const *vals;
            if (rec[kv::PG_FLAG] == 0) {
                vals = rec + kv::PG_PAYLOAD;
            }
            else {
                uint64_t ext_ref;
                std::memcpy(&ext_ref, rec + kv::PG_PAYLOAD, sizeof(ext_ref));
                vals = R(ext_ref);
            }
            size_t rank = 0;
            for (size_t bit = 0; bit < 128; ++bit) {
                if (!kv::bit_test(bm, bit)) {
                    continue;
                }
                std::array<unsigned char, 32> k = base_key;
                k[31] = static_cast<unsigned char>(
                    k[31] | static_cast<unsigned char>(bit));
                std::array<unsigned char, 32> v;
                std::memcpy(v.data(), vals + rank * 32, 32);
                m[k] = v;
                ++rank;
            }
        }
    }

    // Pack sorted (slot,value) pairs into flat storage leaves (one level).
    std::vector<kv::LevelEnt> pack_stor_leaves(
        std::vector<std::pair<bytes32_t, bytes32_t>> const &pairs)
    {
        std::vector<kv::LevelEnt> out;
        constexpr size_t cap = (kv::NODE_SIZE - kv::HDR) / kv::STOR_REC_FLAT;
        size_t const n = pairs.size();
        size_t const k = (n + cap - 1) / cap;
        size_t i = 0;
        for (size_t nj = 0; nj < k; ++nj) {
            size_t const count = split_count(n, cap, nj);
            unsigned char buf[kv::NODE_SIZE];
            std::memset(buf, 0, kv::NODE_SIZE);
            buf[0] = kv::N_LEAF_STORAGE_FLAT;
            buf[1] = static_cast<unsigned char>(kv::STOR_KEY);
            uint16_t const c = static_cast<uint16_t>(count);
            std::memcpy(buf + 2, &c, sizeof(c));
            unsigned char *q = buf + kv::HDR;
            for (size_t j = 0; j < count; ++j) {
                std::memcpy(q, pairs[i + j].first.bytes, 32);
                q += 32;
                std::memcpy(q, pairs[i + j].second.bytes, 32);
                q += 32;
            }
            kv::LevelEnt e;
            std::memcpy(e.key, pairs[i].first.bytes, kv::STOR_KEY);
            e.ref = emit(buf);
            out.push_back(e);
            i += count;
        }
        return out;
    }

    // COW merge-descent of a storage subtree (mirrors merge_acct): rewrite only
    // the touched leaves + spine, share the rest. Emits flat leaves. This is
    // what keeps per-block node output tiny (vs the old full-subtree re-pack).
    std::vector<kv::LevelEnt> merge_stor(
        uint64_t const old_ref, std::vector<kv::SlotUpdate> const &u,
        size_t const lo, size_t const hi)
    {
        kv::NodeReader const R = node_reader();
        unsigned char const *n = R(old_ref);
        if (n[0] != kv::N_INTERNAL) {
            std::map<
                std::array<unsigned char, 32>, std::array<unsigned char, 32>>
                m;
            enumerate_leaf(R, n, m);
            for (size_t j = lo; j < hi; ++j) {
                std::array<unsigned char, 32> k;
                std::memcpy(k.data(), u[j].slot.bytes, 32);
                bool zero = true;
                for (size_t b = 0; b < 32; ++b) {
                    if (u[j].value.bytes[b]) {
                        zero = false;
                        break;
                    }
                }
                if (zero) {
                    m.erase(k);
                }
                else {
                    std::array<unsigned char, 32> v;
                    std::memcpy(v.data(), u[j].value.bytes, 32);
                    m[k] = v;
                }
            }
            std::vector<std::pair<bytes32_t, bytes32_t>> recs;
            recs.reserve(m.size());
            for (auto const &[k, v] : m) {
                bytes32_t s, val;
                std::memcpy(s.bytes, k.data(), 32);
                std::memcpy(val.bytes, v.data(), 32);
                recs.emplace_back(s, val);
            }
            return pack_stor_leaves(recs);
        }
        size_t const kl = n[1];
        size_t const esz = kl + 8;
        unsigned char const *p = n + kv::HDR;
        uint16_t count;
        std::memcpy(&count, n + 2, sizeof(count));
        std::vector<kv::LevelEnt> new_children;
        size_t wj = lo;
        for (size_t i = 0; i < count; ++i) {
            unsigned char const *sep_i = p + i * esz;
            uint64_t child_ref;
            std::memcpy(&child_ref, sep_i + kl, sizeof(child_ref));
            size_t child_hi = wj;
            if (i + 1 < count) {
                unsigned char const *sep_next = p + (i + 1) * esz;
                while (child_hi < hi &&
                       std::memcmp(u[child_hi].slot.bytes, sep_next, kl) < 0) {
                    ++child_hi;
                }
            }
            else {
                child_hi = hi;
            }
            if (child_hi > wj) {
                auto sub = merge_stor(child_ref, u, wj, child_hi);
                for (auto const &e : sub) {
                    new_children.push_back(e);
                }
                wj = child_hi;
            }
            else {
                kv::LevelEnt e;
                std::memcpy(e.key, sep_i, kl);
                e.ref = child_ref;
                new_children.push_back(e);
            }
        }
        MONAD_ASSERT(wj == hi);
        return pack_internal_level(new_children, kl);
    }

    // Merge an account's slot updates into its old storage subtree -> new
    // storage-root ref (NULL_REF if empty). Partial descent: only touched
    // leaves + spine rewritten; untouched nodes shared.
    uint64_t merge_storage(
        uint64_t const old_sref, std::vector<kv::SlotUpdate> const &updates)
    {
        if (old_sref == kv::NULL_REF) {
            // fresh subtree: pack the non-zero updates (already slot-sorted)
            std::vector<std::pair<bytes32_t, bytes32_t>> pairs;
            for (auto const &u : updates) {
                bool zero = true;
                for (size_t b = 0; b < 32; ++b) {
                    if (u.value.bytes[b]) {
                        zero = false;
                        break;
                    }
                }
                if (!zero) {
                    pairs.emplace_back(u.slot, u.value);
                }
            }
            return build_storage_flat(pairs);
        }
        if (updates.empty()) {
            return old_sref;
        }
        std::vector<kv::LevelEnt> ents =
            merge_stor(old_sref, updates, 0, updates.size());
        if (ents.empty()) {
            return kv::NULL_REF;
        }
        while (ents.size() > 1) {
            ents = pack_internal_level(ents, kv::STOR_KEY);
        }
        return ents[0].ref;
    }

    // Pack sorted 108B account records into leaf nodes (one level).
    std::vector<kv::LevelEnt> pack_acct_leaves(
        std::vector<std::array<unsigned char, kv::ACCT_REC>> const &recs)
    {
        std::vector<kv::LevelEnt> out;
        constexpr size_t cap = (kv::NODE_SIZE - kv::HDR) / kv::ACCT_REC;
        size_t const n = recs.size();
        size_t const k = (n + cap - 1) / cap;
        size_t i = 0;
        for (size_t nj = 0; nj < k; ++nj) {
            size_t const count = split_count(n, cap, nj);
            unsigned char buf[kv::NODE_SIZE];
            std::memset(buf, 0, kv::NODE_SIZE);
            buf[0] = kv::N_LEAF_ACCOUNT;
            buf[1] = static_cast<unsigned char>(kv::ACCT_KEY);
            uint16_t const c = static_cast<uint16_t>(count);
            std::memcpy(buf + 2, &c, sizeof(c));
            unsigned char *q = buf + kv::HDR;
            for (size_t j = 0; j < count; ++j) {
                std::memcpy(q, recs[i + j].data(), kv::ACCT_REC);
                q += kv::ACCT_REC;
            }
            kv::LevelEnt e;
            std::memcpy(e.key, recs[i].data(), kv::ACCT_KEY);
            e.ref = emit(buf);
            out.push_back(e);
            i += count;
        }
        return out;
    }

    // Pack (key,ref) entries into internal nodes (one level) — used inside the
    // merge recursion so splits become siblings, not extra levels. Balanced
    // split (split_count) so an overflow yields two ~half-full nodes rather than
    // [full, single-child]; the latter cascaded single-child spillovers up the
    // tree that split-only never reclaimed (see debug_raw_260813a).
    std::vector<kv::LevelEnt> pack_internal_level(
        std::vector<kv::LevelEnt> const &ents, size_t const key_len)
    {
        std::vector<kv::LevelEnt> out;
        size_t const esz = key_len + 8;
        size_t const cap = (kv::NODE_SIZE - kv::HDR) / esz;
        size_t const n = ents.size();
        size_t const k = (n + cap - 1) / cap;
        size_t i = 0;
        for (size_t nj = 0; nj < k; ++nj) {
            size_t const count = split_count(n, cap, nj);
            unsigned char buf[kv::NODE_SIZE];
            std::memset(buf, 0, kv::NODE_SIZE);
            buf[0] = kv::N_INTERNAL;
            buf[1] = static_cast<unsigned char>(key_len);
            uint16_t const c = static_cast<uint16_t>(count);
            std::memcpy(buf + 2, &c, sizeof(c));
            unsigned char *q = buf + kv::HDR;
            for (size_t j = 0; j < count; ++j) {
                std::memcpy(q, ents[i + j].key, key_len);
                q += key_len;
                std::memcpy(q, &ents[i + j].ref, 8);
                q += 8;
            }
            kv::LevelEnt e;
            std::memcpy(e.key, ents[i].key, key_len);
            e.ref = emit(buf);
            out.push_back(e);
            i += count;
        }
        return out;
    }

    // COW merge-descent of the account tree: merge writes[lo,hi) (sorted, all
    // within old_ref's key range) into the subtree at old_ref; returns the new
    // nodes replacing old_ref (empty => subtree emptied). Untouched children
    // keep their old ref (shared, not rewritten). Split-only; drop-empty.
    std::vector<kv::LevelEnt> merge_acct(
        uint64_t const old_ref, std::vector<kv::AcctWrite> const &w,
        size_t const lo, size_t const hi)
    {
        kv::NodeReader const R = node_reader();
        unsigned char const *n = R(old_ref);
        uint16_t count;
        std::memcpy(&count, n + 2, sizeof(count));
        unsigned char const *p = n + kv::HDR;

        if (n[0] == kv::N_LEAF_ACCOUNT) {
            std::map<
                std::array<unsigned char, kv::ACCT_KEY>,
                std::array<unsigned char, kv::ACCT_REC>>
                m;
            for (size_t i = 0; i < count; ++i) {
                unsigned char const *rec = p + i * kv::ACCT_REC;
                std::array<unsigned char, kv::ACCT_KEY> k;
                std::array<unsigned char, kv::ACCT_REC> r;
                std::memcpy(k.data(), rec, kv::ACCT_KEY);
                std::memcpy(r.data(), rec, kv::ACCT_REC);
                m[k] = r;
            }
            for (size_t j = lo; j < hi; ++j) {
                std::array<unsigned char, kv::ACCT_KEY> k;
                std::memcpy(k.data(), w[j].addr.bytes, kv::ACCT_KEY);
                if (w[j].del) {
                    m.erase(k);
                }
                else {
                    std::array<unsigned char, kv::ACCT_REC> r;
                    std::memcpy(r.data(), w[j].rec.data(), kv::ACCT_REC);
                    m[k] = r;
                }
            }
            std::vector<std::array<unsigned char, kv::ACCT_REC>> recs;
            recs.reserve(m.size());
            for (auto const &[k, r] : m) {
                recs.push_back(r);
            }
            return pack_acct_leaves(recs);
        }

        // The old root may be a block root (last block's); its entries are read
        // like an internal node (blob tail ignored — this block writes fresh
        // blobs). merge produces plain internal nodes; merge_account_tree re-emits
        // the new top as the block root.
        MONAD_ASSERT(n[0] == kv::N_INTERNAL || n[0] == kv::N_BLOCK_ROOT);
        size_t const kl = n[1];
        size_t const esz = kl + 8;
        std::vector<kv::LevelEnt> new_children;
        size_t wj = lo;
        for (size_t i = 0; i < count; ++i) {
            unsigned char const *sep_i = p + i * esz;
            uint64_t child_ref;
            std::memcpy(&child_ref, sep_i + kl, sizeof(child_ref));
            // writes for child i = those with addr < sep_{i+1} (all remaining
            // for the last child). Keys below sep_0 fall to child 0.
            size_t child_hi = wj;
            if (i + 1 < count) {
                unsigned char const *sep_next = p + (i + 1) * esz;
                while (child_hi < hi &&
                       std::memcmp(w[child_hi].addr.bytes, sep_next, kl) < 0) {
                    ++child_hi;
                }
            }
            else {
                child_hi = hi;
            }
            if (child_hi > wj) {
                auto sub = merge_acct(child_ref, w, wj, child_hi);
                for (auto const &e : sub) {
                    new_children.push_back(e);
                }
                wj = child_hi;
            }
            else {
                kv::LevelEnt e;
                std::memcpy(e.key, sep_i, kl);
                e.ref = child_ref;
                new_children.push_back(e);
            }
        }
        MONAD_ASSERT(wj == hi);
        return pack_internal_level(new_children, kl);
    }

    // The account-tree top's child entries (what a block root packs). For an
    // internal/block-root node these are its entries (blob tail ignored); for a
    // leaf root (tiny state) it is one entry wrapping the leaf.
    std::vector<kv::LevelEnt> top_entries(uint64_t const root)
    {
        kv::NodeReader const R = node_reader();
        unsigned char const *const n = R(root);
        std::vector<kv::LevelEnt> ents;
        if (n[0] == kv::N_INTERNAL || n[0] == kv::N_BLOCK_ROOT) {
            size_t const kl = n[1];
            uint16_t count;
            std::memcpy(&count, n + 2, sizeof(count));
            unsigned char const *const p = n + kv::HDR;
            for (size_t i = 0; i < count; ++i) {
                kv::LevelEnt e;
                std::memcpy(e.key, p + i * (kl + 8), kl);
                std::memcpy(&e.ref, p + i * (kl + 8) + kl, 8);
                ents.push_back(e);
            }
        }
        else { // leaf root: wrap as a single entry keyed by its first record
            kv::LevelEnt e;
            std::memcpy(e.key, n + kv::HDR, kv::ACCT_KEY);
            e.ref = root;
            ents.push_back(e);
        }
        return ents;
    }

    // Emit the account-tree top as the block root: an internal-style node
    // (entries at HDR) whose tail carries this block's blob roots. Capacity is
    // reserved by the caller (entries fit below BLOCK_ROOT_BLOB_OFF).
    uint64_t emit_block_root(
        std::vector<kv::LevelEnt> const &ents, size_t const key_len,
        kv::BlobRoots const &blobs)
    {
        unsigned char buf[kv::NODE_SIZE];
        std::memset(buf, 0, kv::NODE_SIZE);
        buf[0] = kv::N_BLOCK_ROOT;
        buf[1] = static_cast<unsigned char>(key_len);
        uint16_t const c = static_cast<uint16_t>(ents.size());
        std::memcpy(buf + 2, &c, sizeof(c));
        unsigned char *q = buf + kv::HDR;
        for (auto const &e : ents) {
            std::memcpy(q, e.key, key_len);
            q += key_len;
            std::memcpy(q, &e.ref, 8);
            q += 8;
        }
        std::memcpy(buf + kv::BLOCK_ROOT_BLOB_OFF, blobs.r, kv::BLOB_N * 8);
        return emit(buf);
    }

    // Apply sorted account writes to the account tree; returns the new block
    // root (an N_BLOCK_ROOT packing the account top + this block's blob roots).
    uint64_t merge_account_tree(
        std::vector<kv::AcctWrite> const &writes, kv::BlobRoots const &blobs)
    {
        // The account top's child entries: unchanged (root_'s children, shared)
        // when there are no state writes, else the merged result. Either way this
        // block gets its OWN block root carrying its blobs.
        std::vector<kv::LevelEnt> ents;
        if (writes.empty()) {
            ents = top_entries(root_);
        }
        else {
            ents = merge_acct(root_, writes, 0, writes.size());
            if (ents.empty()) {
                return kv::NULL_REF; // state emptied
            }
        }
        // Pack full-capacity internal levels until the remaining top entries fit
        // in the block root alongside its reserved blob tail; then emit that top
        // as the block root. Worst case (a near-full root) adds one level.
        size_t const esz = kv::ACCT_KEY + 8;
        while (kv::HDR + ents.size() * esz > kv::BLOCK_ROOT_BLOB_OFF) {
            ents = pack_internal_level(ents, kv::ACCT_KEY);
        }
        return emit_block_root(ents, kv::ACCT_KEY, blobs);
    }

    // items 2+3: apply one block's updates to KV and install the new root.
    // Runs on the DB io service thread; reads/writes go through KV's own fd
    // (kv_fd_) at flat device offsets, not triedb's storage_pool.
    // ── block map access ────────────────────────────────────────────────
    // Key = (block big-endian 8B, id 32B). Big-endian block so a byte compare
    // orders by block then id.
    // Value layout (BM_VL bytes):
    //   [0]  block_root   8B   this block's top-level root. With no blobs it is
    //                          the state root; once blobs exist it is a block
    //                          root node whose children are the state root + the
    //                          blob roots. It is the single HP2-protected,
    //                          separately-retired root per block; state + blobs
    //                          are its link-counted children (cascade-freed).
    //   [8]  parent_id    32B  parent proposal's block_id
    //   [40] block_hash   32B  this block's eth hash H (keccak(rlp(header)));
    //                          drives block_hash-index prune and is the
    //                          number->hash value. Zero when unknown.
    static constexpr size_t BM_HASH_OFF = 40; // block_hash H
    static constexpr size_t BM_KL = 40, BM_VL = BM_HASH_OFF + 32;
    static void
    bm_key(unsigned char *const out, uint64_t const block, bytes32_t const &id)
    {
        for (int i = 0; i < 8; ++i) {
            out[i] = static_cast<unsigned char>(block >> (56 - 8 * i));
        }
        std::memcpy(out + 8, id.bytes, 32);
    }
    static uint64_t bm_block(unsigned char const *const key)
    {
        uint64_t b = 0;
        for (int i = 0; i < 8; ++i) {
            b = (b << 8) | key[i];
        }
        return b;
    }
    static void bm_val(
        unsigned char *const out, uint64_t const block_root,
        bytes32_t const &parent_id,
        bytes32_t const &block_hash = bytes32_t{})
    {
        std::memcpy(out, &block_root, 8);
        std::memcpy(out + 8, parent_id.bytes, 32);
        std::memcpy(out + BM_HASH_OFF, block_hash.bytes, 32);
    }
    // Page store for the block map over this KV's pages: read copies a page into
    // a per-store buffer (valid until the next read); emit appends a new page.
    struct KvStore
    {
        KvShadow *kv;
        std::array<unsigned char, kv::NODE_SIZE> buf;
        uint64_t reads = 0; // pages read via this store (code-read stats)
        uint64_t io = 0; // of those, device reads (cache misses)
        // Maintain link counts on emit. True for the reclaimable state block map;
        // false for the grow-only code tree + code pages (never reclaimed, and
        // raw code data pages are untyped so must not be walked as nodes).
        bool count_links = true;
        unsigned char const *read(uint64_t const ref)
        {
            ++reads;
            kv::NodeCache::ConstAccessor acc;
            if (kv->cache_.find(acc, ref)) {
                std::memcpy(buf.data(), acc->second->val.data(), kv::NODE_SIZE);
            }
            else {
                ssize_t const r = ::pread(
                    kv->kv_fd_, buf.data(), kv::NODE_SIZE,
                    static_cast<off_t>(kv->kv_base_ + ref));
                MONAD_ASSERT(r == static_cast<ssize_t>(kv::NODE_SIZE));
                ++io;
                kv->cache_.insert(ref, buf); // populate so repeats hit the cache
            }
            return buf.data();
        }
        uint64_t emit(unsigned char const *const page)
        {
            uint64_t const ref = kv->allocate_page();
            std::array<unsigned char, kv::NODE_SIZE> pg;
            std::memcpy(pg.data(), page, kv::NODE_SIZE);
            kv->cache_.insert(ref, pg);
            kv->kvio().submit_write(ref, pg.data());
            kv->kvio().drain();
            if (count_links) {
                kv->inc_children(page); // one link per child this page points to
            }
            return ref;
        }
    };
    // State root of a finalized block via the block map (reads + validation).
    uint64_t finalized_state_root(uint64_t const block)
    {
        KvStore st{this};
        unsigned char probe[BM_KL], k[BM_KL], v[BM_VL];
        bm_key(probe, block, bytes32_t{});
        if (!kv::blockmap::lower_bound(
                st, meta_->tree_root, probe, BM_KL, BM_VL, k, v)) {
            return kv::NULL_REF;
        }
        if (bm_block(k) != block) {
            return kv::NULL_REF;
        }
        uint64_t sr;
        std::memcpy(&sr, v, 8);
        return sr;
    }

    // ── code store (grow-only, content-addressed) ───────────────────────
    // code_tree_root maps code_hash (32B) -> code root page ref (8B). The root
    // page is either N_CODE_INLINE (whole code in the page) or N_CODE_INDEX
    // (len + child count + child refs to raw data pages). Read is 1 io (inline)
    // or 1 + child ios (index); never deeper.
    static constexpr size_t CODE_LEN = 8; // u64 total length
    static constexpr size_t CODE_NCHILD = 16; // u32 child count (index)
    static constexpr size_t CODE_CHILDREN = 24; // u64 child refs[] (index)
    static constexpr size_t CODE_INLINE_OFF = 16; // inline bytes
    static constexpr size_t CODE_INLINE_CAP = kv::NODE_SIZE - CODE_INLINE_OFF;
    static constexpr size_t CODE_MAX_CHILDREN =
        (kv::NODE_SIZE - CODE_CHILDREN) / 8;

    // Write a per-block blob wholly inside one page (N_BLOB_INLINE), returning
    // its ref. Link-counted via the state-tree emit() (so it is reclaimed with
    // the block root that owns it). Layout mirrors N_CODE_INLINE: len at
    // CODE_LEN, bytes at CODE_INLINE_OFF. For blobs larger than CODE_INLINE_CAP
    // a multi-page N_BLOB_INDEX form is added with the first such category.
    uint64_t write_blob_inline(unsigned char const *const data, size_t const len)
    {
        MONAD_ASSERT(len <= CODE_INLINE_CAP);
        unsigned char pg[kv::NODE_SIZE];
        std::memset(pg, 0, kv::NODE_SIZE);
        pg[0] = kv::N_BLOB_INLINE;
        uint64_t const l = len;
        std::memcpy(pg + CODE_LEN, &l, 8);
        std::memcpy(pg + CODE_INLINE_OFF, data, len);
        return emit(pg);
    }

    // Write one blob: inline (N_BLOB_INLINE) if it fits a page, else an
    // N_BLOB_INDEX root over raw data pages. Returns the root, NULL_REF if empty.
    uint64_t write_blob(unsigned char const *const data, size_t const len)
    {
        if (len == 0) {
            return kv::NULL_REF;
        }
        if (len <= CODE_INLINE_CAP) {
            return write_blob_inline(data, len);
        }
        // Data pages, then one or more levels of index over them. A single
        // index page holds CODE_MAX_CHILDREN refs; past that the refs are
        // themselves index pages, and pg[1] carries the height so a reader
        // knows whether a child is data (0) or another index (>0). Height 0 is
        // byte-for-byte the single-level form, so images written before this
        // read unchanged.
        size_t const np = (len + kv::NODE_SIZE - 1) / kv::NODE_SIZE;
        std::vector<uint64_t> refs(np);
        for (size_t i = 0; i < np; ++i) {
            unsigned char d[kv::NODE_SIZE];
            std::memset(d, 0, kv::NODE_SIZE); // tail zero-pad
            size_t const n =
                std::min<size_t>(kv::NODE_SIZE, len - i * kv::NODE_SIZE);
            std::memcpy(d, data + i * kv::NODE_SIZE, n);
            refs[i] = emit_raw(d); // raw: link taken by the index's inc_children
        }
        // `len` on every level is the length of the range that level covers, so
        // a reader can size each child's contribution without extra state.
        auto const emit_index = [this](
                                    std::vector<uint64_t> const &children,
                                    uint8_t const height,
                                    uint64_t const covered) {
            unsigned char pg[kv::NODE_SIZE];
            std::memset(pg, 0, kv::NODE_SIZE);
            pg[0] = kv::N_BLOB_INDEX;
            pg[1] = height;
            std::memcpy(pg + CODE_LEN, &covered, 8);
            uint32_t const nc = static_cast<uint32_t>(children.size());
            std::memcpy(pg + CODE_NCHILD, &nc, 4);
            std::memcpy(pg + CODE_CHILDREN, children.data(), nc * 8);
            return emit(pg);
        };
        size_t const fan = blob_fanout();
        uint8_t height = 0;
        // Bytes one child at this height covers: a data page, then `fan` of
        // whatever the level below covered.
        uint64_t span = kv::NODE_SIZE;
        while (refs.size() > fan) {
            std::vector<uint64_t> up;
            up.reserve((refs.size() + fan - 1) / fan);
            for (size_t i = 0; i < refs.size(); i += fan) {
                size_t const n = std::min<size_t>(fan, refs.size() - i);
                std::vector<uint64_t> const group(
                    refs.begin() + static_cast<ptrdiff_t>(i),
                    refs.begin() + static_cast<ptrdiff_t>(i + n));
                uint64_t const covered =
                    std::min<uint64_t>(len - i * span, n * span);
                up.push_back(emit_index(group, height, covered));
            }
            refs.swap(up);
            span *= fan;
            ++height;
        }
        return emit_index(refs, height, len);
    }

    // Write a per-block table (N_BLOB_TABLE): entry i is one blob root, indexed
    // by position (e.g. tx_index). Returns the table root, NULL_REF if empty.
    static constexpr size_t BLOB_TABLE_MAX = (kv::NODE_SIZE - kv::HDR) / 8;
    // Refs per page for the multi-level blob forms. The real value is what a
    // 4KB page holds; $KVDB_BLOB_FANOUT shrinks it so the levels above the
    // first are reachable with ordinary mainnet blocks, which are far too small
    // to build one otherwise. Read once. Only the WRITE side consults this --
    // both node forms carry what a reader needs (an index its child count, a
    // table its per-child span), so an image stays readable whatever it was
    // written with.
    static size_t blob_fanout()
    {
        static size_t const fan = [] {
            constexpr size_t real = BLOB_TABLE_MAX < CODE_MAX_CHILDREN
                                        ? BLOB_TABLE_MAX
                                        : CODE_MAX_CHILDREN;
            char const *const e = std::getenv("KVDB_BLOB_FANOUT");
            if (e == nullptr) {
                return real;
            }
            size_t const v = std::strtoull(e, nullptr, 10);
            MONAD_ASSERT(v >= 2 && v <= real);
            return v;
        }();
        return fan;
    }
    uint64_t write_blob_table(
        std::vector<std::pair<unsigned char const *, size_t>> const &items)
    {
        if (items.empty()) {
            return kv::NULL_REF;
        }
        std::vector<uint64_t> refs;
        refs.reserve(items.size());
        for (auto const &[p, n] : items) {
            refs.push_back(write_blob(p, n));
        }
        // One page holds BLOB_TABLE_MAX refs; past that the refs are child
        // tables and pg[1] carries the height, so entry i is reached by radix
        // decomposition on BLOB_TABLE_MAX. Height 0 is byte-for-byte the
        // single-level form. The count stays u16: it is bounded by the
        // protocol's transactions-per-block limit, far below 65535.
        auto const emit_table = [this](
                                    std::vector<uint64_t> const &children,
                                    uint8_t const height,
                                    size_t const covered,
                                    size_t const child_span) {
            unsigned char pg[kv::NODE_SIZE];
            std::memset(pg, 0, kv::NODE_SIZE);
            pg[0] = kv::N_BLOB_TABLE;
            pg[1] = height;
            uint16_t const c = static_cast<uint16_t>(covered);
            std::memcpy(pg + 2, &c, sizeof(c));
            // Above height 0, store how many entries ONE CHILD covers (bytes
            // 4..8, previously unused). That makes the node self-describing:
            // the child count is ceil(count / span), so no reader needs to know
            // the fan-out the writer used -- which is what lets the fan-out be
            // shrunk for testing without changing how images are read. Only
            // read when height > 0, so tables written before this field existed
            // (all of them height 0) still walk by their count.
            uint32_t const sp = static_cast<uint32_t>(child_span);
            std::memcpy(pg + 4, &sp, sizeof(sp));
            std::memcpy(pg + kv::HDR, children.data(), children.size() * 8);
            return emit(pg);
        };
        size_t const fan = blob_fanout();
        uint8_t height = 0;
        size_t span = 1; // entries covered by one child at this height
        size_t const total = refs.size();
        while (refs.size() > fan) {
            std::vector<uint64_t> up;
            up.reserve((refs.size() + fan - 1) / fan);
            for (size_t i = 0; i < refs.size(); i += fan) {
                size_t const n = std::min<size_t>(fan, refs.size() - i);
                std::vector<uint64_t> const group(
                    refs.begin() + static_cast<ptrdiff_t>(i),
                    refs.begin() + static_cast<ptrdiff_t>(i + n));
                up.push_back(emit_table(
                    group, height, std::min(total - i * span, n * span), span));
            }
            refs.swap(up);
            span *= fan;
            ++height;
        }
        return emit_table(refs, height, total, span);
    }

    // Write the code as pages, return its root page ref.
    uint64_t
    write_code_pages(KvStore &st, unsigned char const *const code, size_t const len)
    {
        std::array<unsigned char, kv::NODE_SIZE> pg{};
        if (len <= CODE_INLINE_CAP) {
            pg[0] = kv::N_CODE_INLINE;
            uint64_t const l = len;
            std::memcpy(pg.data() + CODE_LEN, &l, 8);
            std::memcpy(pg.data() + CODE_INLINE_OFF, code, len);
            return st.emit(pg.data());
        }
        size_t const np = (len + kv::NODE_SIZE - 1) / kv::NODE_SIZE;
        MONAD_ASSERT(np <= CODE_MAX_CHILDREN);
        std::vector<uint64_t> refs(np);
        for (size_t i = 0; i < np; ++i) {
            std::array<unsigned char, kv::NODE_SIZE> d{};
            size_t const n =
                std::min<size_t>(kv::NODE_SIZE, len - i * kv::NODE_SIZE);
            std::memcpy(d.data(), code + i * kv::NODE_SIZE, n); // tail zero-pad
            refs[i] = st.emit(d.data());
        }
        pg[0] = kv::N_CODE_INDEX;
        uint64_t const l = len;
        std::memcpy(pg.data() + CODE_LEN, &l, 8);
        uint32_t const nc = static_cast<uint32_t>(np);
        std::memcpy(pg.data() + CODE_NCHILD, &nc, 4);
        std::memcpy(pg.data() + CODE_CHILDREN, refs.data(), np * 8);
        return st.emit(pg.data());
    }

    // Write this block's new code into the code B+tree, dedup by hash.
    void write_code(Code const &code)
    {
        if (code.empty()) {
            return;
        }
        KvStore st{this};
        st.count_links = false; // code tree + code pages are grow-only
        for (auto const &[hash, icode] : code) {
            unsigned char v[8];
            if (kv::blockmap::lookup(
                    st, meta_->code_tree_root, hash.bytes, 32, 8, v)) {
                continue; // already present (content-addressed)
            }
            uint64_t const root =
                write_code_pages(st, icode->code(), icode->size());
            unsigned char val[8];
            std::memcpy(val, &root, 8);
            meta_->code_tree_root = kv::blockmap::insert(
                st, meta_->code_tree_root, hash.bytes, val, 32, 8);
        }
        std::atomic_thread_fence(std::memory_order_release);
        ::msync(meta_map_, KVDB_META_BYTES, MS_ASYNC);
    }

    // Read the code at a root page ref (inline page, or index page + data
    // pages). Runs on the io thread.
    // Read the code at a root page ref. Runs on the io thread. The data pages
    // of an index-coded blob are fetched in ONE parallel io_uring batch (the
    // page-tree's point), not one blocking read at a time; cache-warm pages are
    // copied directly. st accumulates page-read (depth) and device-read (io)
    // counts for the kv_code metric.
    byte_string read_code_pages(KvStore &st, uint64_t const ref)
    {
        unsigned char const *const p = st.read(ref);
        uint64_t len;
        std::memcpy(&len, p + CODE_LEN, 8);
        byte_string out;
        out.resize(len);
        if (p[0] == kv::N_CODE_INLINE) {
            std::memcpy(out.data(), p + CODE_INLINE_OFF, len);
            return out;
        }
        uint32_t nc;
        std::memcpy(&nc, p + CODE_NCHILD, 4);
        std::vector<uint64_t> refs(nc); // snapshot before reading children
        std::memcpy(refs.data(), p + CODE_CHILDREN, nc * 8);
        uint64_t parallel = 0;
        for (uint32_t i = 0; i < nc; ++i) {
            ++st.reads;
            size_t const off = static_cast<size_t>(i) * kv::NODE_SIZE;
            size_t const n = std::min<size_t>(kv::NODE_SIZE, len - off);
            kv::NodeCache::ConstAccessor acc;
            if (cache_.find(acc, refs[i])) { // warm: copy directly
                std::memcpy(out.data() + off, acc->second->val.data(), n);
            }
            else { // cold: fetch in the parallel batch below
                ++st.io;
                ++parallel;
                kvio().submit_read(
                    refs[i],
                    [dst = out.data() + off, n](
                        unsigned char const *const d, bool) {
                        std::memcpy(dst, d, n);
                    });
            }
        }
        kvio().drain(); // reap the whole batch (parallel, one submit)
        if (nc > 0) {
            code_multipage_reads.fetch_add(1, std::memory_order_relaxed);
            code_parallel_io.fetch_add(parallel, std::memory_order_relaxed);
        }
        return out;
    }

    // Look up code by hash; nullopt if absent. Runs on the io thread.
    std::optional<byte_string> lookup_code(bytes32_t const &hash)
    {
        KvStore st{this};
        unsigned char v[8];
        std::optional<byte_string> out;
        if (kv::blockmap::lookup(
                st, meta_->code_tree_root, hash.bytes, 32, 8, v)) {
            uint64_t root;
            std::memcpy(&root, v, 8);
            out = read_code_pages(st, root);
        }
        // stats: the B+tree descent plus the code page reads (analog to
        // triedb's trie_code full descent). depth = pages read, io = device reads.
        KVDB_ADD(
            ::monad::kvdb_metrics::kv_code, static_cast<uint32_t>(st.reads),
            static_cast<uint32_t>(st.io));
        return out;
    }

    void commit_block(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io,
        std::vector<kv::AccountUpdates> const &ups, uint64_t const block,
        bytes32_t const &block_id, bytes32_t const &block_hash,
        byte_string const &header_rlp, CommitBuilder const &builder)
    {
        if (write_pos_ == 0) {
            // new nodes begin right after the base image (continuing the same
            // logical-ref => device-position mapping the builder established).
            write_pos_ = image_bytes;
        }
        // Start this block's write buffer.
        ++blocks_committed_;
        wbuf_.clear();
        wref_.clear();
        wbuf_index_.clear();
        // Async prefetch this block's read set (ancestry paths of all updated
        // keys) so the synchronous build below hits cache rather than blocking
        // on the NodeReader's fallback ::pread.
        prefetch_updates(io, ups);
        kv::NodeReader const R = node_reader();
        std::vector<kv::AcctWrite> writes;
        writes.reserve(ups.size());
        for (auto const &au : ups) {
            kv::AcctWrite wr;
            wr.addr = au.addr;
            unsigned char const *oldrec = kv::find_account(R, root_, au.addr);
            uint64_t old_sref = kv::NULL_REF;
            if (oldrec) {
                std::memcpy(&old_sref, oldrec + 20 + sizeof(Account), 8);
            }
            if (au.op == kv::AcctOp::Delete) {
                wr.del = true;
            }
            else {
                wr.del = false;
                uint64_t const new_sref = merge_storage(old_sref, au.slots);
                std::memcpy(wr.rec.data(), au.addr.bytes, 20);
                std::memcpy(wr.rec.data() + 20, &au.account, sizeof(Account));
                std::memcpy(
                    wr.rec.data() + 20 + sizeof(Account), &new_sref, 8);
            }
            writes.push_back(wr);
        }
        // Build this block's blobs, then pack their roots into the block root.
        // All values are REUSED from the CommitBuilder's already-encoded,
        // DB-format byte-strings (byte-identical to triedb) — no re-encode on the
        // commit critical path. Header is the RLP we encoded once for H (inline).
        kv::BlobRoots blobs;
        if (!header_rlp.empty()) {
            blobs.r[kv::BLOB_HEADER] =
                write_blob_inline(header_rlp.data(), header_rlp.size());
        }
        auto to_items = [](std::vector<byte_string_view> const &vs) {
            std::vector<std::pair<unsigned char const *, size_t>> items;
            items.reserve(vs.size());
            for (auto const &v : vs) {
                items.emplace_back(v.data(), v.size());
            }
            return items;
        };
        // Per-tx categories -> a per-block table keyed by tx_index.
        if (!builder.kv_receipts().empty()) {
            blobs.r[kv::BLOB_RECEIPTS] =
                write_blob_table(to_items(builder.kv_receipts()));
        }
        if (!builder.kv_transactions().empty()) {
            blobs.r[kv::BLOB_TXNS] =
                write_blob_table(to_items(builder.kv_transactions()));
        }
        if (!builder.kv_call_frames().empty()) {
            blobs.r[kv::BLOB_CALLFRAMES] =
                write_blob_table(to_items(builder.kv_call_frames()));
        }
        if (!builder.kv_withdrawals().empty()) {
            blobs.r[kv::BLOB_WITHDRAWALS] =
                write_blob_table(to_items(builder.kv_withdrawals()));
        }
        // Single-blob categories.
        if (!builder.kv_ommers().empty()) {
            blobs.r[kv::BLOB_OMMERS] =
                write_blob(builder.kv_ommers().data(), builder.kv_ommers().size());
        }
        // tx-hash list (32B each, concatenated) -> one blob, for tx-index prune.
        if (!builder.kv_tx_hashes().empty()) {
            byte_string hashes;
            hashes.reserve(builder.kv_tx_hashes().size() * 32);
            for (auto const &h : builder.kv_tx_hashes()) {
                hashes.append(h.data(), h.size());
            }
            blobs.r[kv::BLOB_TXHASHES] = write_blob(hashes.data(), hashes.size());
        }
        // ups (and thus writes) are already sorted by address. root_ becomes
        // this block's block root (account top packed with the blob roots).
        root_ = merge_account_tree(writes, blobs);
        // Write pass: flush this block's new nodes to the device and cache
        // them, then release the RAM buffer. Refs were assigned at build time
        // (write_pos_), so no fix-up is needed.
        write_block_nodes(io);
        // Insert this proposal into the block map: key = (block, id), value =
        // (state root, parent id). The parent was positioned by set_tip. No
        // finalized write here; the frontier advances at finalize.
        KvStore st{this};
        unsigned char key[BM_KL], val[BM_VL];
        bm_key(key, block, block_id);
        bm_val(val, root_, cur_parent_id_, block_hash);
        // The state root's single "present in block map" link (state roots are
        // not counted per block-map leaf). Removed when this block is pruned or
        // this proposal loses, which retires the state root.
        link_inc(root_);
        // Install the new block-map root: adds the metadata-pointer link and
        // retires the superseded old root.
        install_block_map_root(kv::blockmap::insert(
            st, meta_->tree_root, key, val, BM_KL, BM_VL));
        // Global hash indexes: insert this block's entries (reuses the builder's
        // tx hashes + the block hash H already in the leaf). Deleted at prune.
        {
            auto const &txh = builder.kv_tx_hashes();
            for (uint32_t i = 0; i < static_cast<uint32_t>(txh.size()); ++i) {
                unsigned char tv[TXH_VL];
                std::memcpy(tv, &block, 8);
                std::memcpy(tv + 8, &i, 4);
                install_index_root(
                    meta_->txhash_index_root,
                    kv::blockmap::insert(
                        st, meta_->txhash_index_root, txh[i].data(), tv,
                        TXH_KL, TXH_VL));
            }
            unsigned char bv[BLKH_VL];
            std::memcpy(bv, &block, 8);
            install_index_root(
                meta_->blockhash_index_root,
                kv::blockmap::insert(
                    st, meta_->blockhash_index_root, block_hash.bytes, bv,
                    BLKH_KL, BLKH_VL));
        }
        std::atomic_thread_fence(std::memory_order_release);
        ::msync(meta_map_, KVDB_META_BYTES, MS_ASYNC);
    }

    // Link-count validator (env KVDB_LCCHECK=1, run at teardown). Traverse the
    // set reachable from the current block-map root, tally each node's
    // structural reference count (child links + the metadata pointer for the
    // root), and check maintained count >= structural for every node. Maintained
    // may exceed structural (older un-released versions still link shared nodes),
    // but never fall below it — a value below means a missed inc. Reports the
    // number of violations. One-sided by design; exact equality is validated by
    // the controlled self-test, not on real accumulated history.
    // Find up to `want` storage pages whose values are stored OUT OF LINE
    // (PG_FLAG != 0), returning every populated slot in them as
    // (address, slot) pairs. These pages hold 127-128 populated slots, so they
    // are ~0.03% of records and a sampled read essentially never lands on one --
    // which is why the readers' ext-ref branch needs them handed to it
    // explicitly. Read-only: walks accounts, then each account's storage
    // subtree, and touches no link counts.
    std::vector<std::pair<Address, bytes32_t>>
    find_ext_page_slots(size_t const want)
    {
        std::vector<std::pair<Address, bytes32_t>> out;
        uint64_t const block_root = finalized_state_root(meta_->finalized_block);
        if (block_root == kv::NULL_REF) {
            return out;
        }
        std::array<unsigned char, kv::NODE_SIZE> buf;
        auto const rd = [&](uint64_t const ref) -> unsigned char const * {
            ssize_t const r = ::pread(
                kv_fd_, buf.data(), kv::NODE_SIZE,
                static_cast<off_t>(kv_base_ + ref));
            MONAD_ASSERT(r == static_cast<ssize_t>(kv::NODE_SIZE));
            return buf.data();
        };
        // Walk one account's storage subtree for out-of-line pages.
        size_t found = 0;
        auto const scan_storage = [&](Address const &addr, uint64_t const sref) {
            std::vector<uint64_t> st{sref};
            while (!st.empty() && found < want) {
                uint64_t const ref = st.back();
                st.pop_back();
                std::array<unsigned char, kv::NODE_SIZE> local;
                std::memcpy(local.data(), rd(ref), kv::NODE_SIZE);
                unsigned char const *const n = local.data();
                if (n[0] == kv::N_LEAF_STORAGE_PAGE) {
                    uint16_t count;
                    std::memcpy(&count, n + 2, sizeof(count));
                    for (size_t i = 0; i < count && found < want; ++i) {
                        uint16_t off;
                        std::memcpy(&off, n + kv::HDR + i * 2, sizeof(off));
                        unsigned char const *const rec = n + off;
                        if (rec[kv::PG_FLAG] == 0) {
                            continue;
                        }
                        ++found;
                        bytes32_t base{};
                        std::memcpy(base.bytes, rec + kv::PG_BASE, 32);
                        for (size_t bit = 0; bit < 128; ++bit) {
                            if (!kv::bit_test(rec + kv::PG_BITMAP, bit)) {
                                continue;
                            }
                            bytes32_t slot = base;
                            slot.bytes[31] = static_cast<unsigned char>(
                                (base.bytes[31] & 0x80) |
                                static_cast<unsigned char>(bit));
                            out.emplace_back(addr, slot);
                        }
                    }
                    continue; // leaves have no node children to descend
                }
                for_each_child_ref(
                    n, [&](uint64_t const c, ChildKind const k) {
                        if (k != ChildKind::Terminal) {
                            st.push_back(c);
                        }
                    });
            }
        };
        std::vector<uint64_t> stack{block_root};
        std::unordered_set<uint64_t> seen{block_root};
        while (!stack.empty() && found < want) {
            uint64_t const ref = stack.back();
            stack.pop_back();
            std::array<unsigned char, kv::NODE_SIZE> local;
            std::memcpy(local.data(), rd(ref), kv::NODE_SIZE);
            unsigned char const *const n = local.data();
            if (n[0] == kv::N_LEAF_ACCOUNT) {
                uint16_t count;
                std::memcpy(&count, n + 2, sizeof(count));
                for (size_t i = 0; i < count && found < want; ++i) {
                    unsigned char const *const rec =
                        n + kv::HDR + i * kv::ACCT_REC;
                    Address addr;
                    std::memcpy(addr.bytes, rec, 20);
                    uint64_t sref;
                    std::memcpy(&sref, rec + 20 + sizeof(Account), 8);
                    if (sref != kv::NULL_REF) {
                        scan_storage(addr, sref);
                    }
                }
                continue;
            }
            for_each_child_ref(n, [&](uint64_t const c, ChildKind const k) {
                if (k != ChildKind::Terminal && seen.insert(c).second) {
                    stack.push_back(c);
                }
            });
        }
        return out;
    }

    // Validation (env KVDB_PGTALLY=1): tally storage-page records by how many
    // slots they hold, split by whether the values are inline or in a separate
    // node. Read-only: walks the live tree and touches no link counts, so it
    // runs on an image as loaded, before any commit. The 127-vs-128 split
    // decides whether a layout that special-cases a fully populated page buys
    // anything, and it is not recorded in the image header.
    void pgtally()
    {
        std::vector<uint64_t> stack;
        std::unordered_set<uint64_t> seen;
        uint64_t const root = meta_->tree_root;
        if (root == kv::NULL_REF) {
            std::fprintf(stderr, "KVDB_PGTALLY: empty tree\n");
            return;
        }
        stack.push_back(root);
        seen.insert(root);
        std::array<unsigned char, kv::NODE_SIZE> buf;
        uint64_t inl = 0, e128 = 0, e127 = 0, eother = 0;
        std::array<uint64_t, 129> inline_hist{};
        while (!stack.empty()) {
            uint64_t const ref = stack.back();
            stack.pop_back();
            ssize_t const r = ::pread(
                kv_fd_, buf.data(), kv::NODE_SIZE,
                static_cast<off_t>(kv_base_ + ref));
            MONAD_ASSERT(r == static_cast<ssize_t>(kv::NODE_SIZE));
            unsigned char const *const n = buf.data();
            if (n[0] == kv::N_LEAF_STORAGE_PAGE) {
                uint16_t count;
                std::memcpy(&count, n + 2, sizeof(count));
                for (size_t i = 0; i < count; ++i) {
                    uint16_t off;
                    std::memcpy(&off, n + kv::HDR + i * 2, sizeof(off));
                    unsigned char const *const rec = n + off;
                    size_t pc = 0;
                    for (size_t b = 0; b < 16; ++b) {
                        pc += static_cast<size_t>(
                            __builtin_popcount(rec[kv::PG_BITMAP + b]));
                    }
                    if (rec[kv::PG_FLAG] == 0) {
                        ++inl;
                        ++inline_hist[pc];
                    }
                    else if (pc == 128) {
                        ++e128;
                    }
                    else if (pc == 127) {
                        ++e127;
                    }
                    else {
                        ++eother; // below the inline limit: unexpected
                    }
                }
            }
            for_each_child_ref(
                n, [&](uint64_t const c, ChildKind const k) {
                    if (k != ChildKind::Terminal && seen.insert(c).second) {
                        stack.push_back(c);
                    }
                });
        }
        std::fprintf(
            stderr,
            "KVDB_PGTALLY: storage pages inline=%llu ext[128]=%llu "
            "ext[127]=%llu ext[other]=%llu\n",
            static_cast<unsigned long long>(inl),
            static_cast<unsigned long long>(e128),
            static_cast<unsigned long long>(e127),
            static_cast<unsigned long long>(eother));
        // The inline tail says how close the population gets to the limit,
        // which is what a denser inline form would have to beat.
        std::fprintf(stderr, "KVDB_PGTALLY: inline popcount tail");
        for (size_t pc = 120; pc <= 126; ++pc) {
            std::fprintf(
                stderr,
                " [%zu]=%llu",
                pc,
                static_cast<unsigned long long>(inline_hist[pc]));
        }
        std::fprintf(stderr, "\n");
    }

    void lc_check()
    {
        std::unordered_map<uint64_t, uint32_t> structural;
        std::vector<uint64_t> stack;
        std::unordered_set<uint64_t> seen;
        uint64_t const root = meta_->tree_root;
        if (root == kv::NULL_REF) {
            return;
        }
        structural[root] += 1; // the metadata pointer
        stack.push_back(root);
        seen.insert(root);
        std::array<unsigned char, kv::NODE_SIZE> buf;
        auto read = [&](uint64_t const ref) -> unsigned char const * {
            ssize_t const r = ::pread(
                kv_fd_, buf.data(), kv::NODE_SIZE,
                static_cast<off_t>(kv_base_ + ref));
            MONAD_ASSERT(r == static_cast<ssize_t>(kv::NODE_SIZE));
            return buf.data();
        };
        while (!stack.empty()) {
            uint64_t const ref = stack.back();
            stack.pop_back();
            unsigned char const *const n = read(ref);
            for_each_child_ref(n, [&](uint64_t const c, ChildKind const k) {
                // A state root is named by exactly one current block-map entry,
                // so its structural count is 1 = its "present" link; count it and
                // descend into its state subtree. Terminal raw pages are counted
                // but never read as nodes.
                structural[c] += 1;
                if (k != ChildKind::Terminal && seen.insert(c).second) {
                    stack.push_back(c);
                }
            });
        }
        uint64_t violations = 0;
        for (auto const &[ref, want] : structural) {
            uint32_t const got =
                pageslot_[ref / kv::NODE_SIZE].load(std::memory_order_relaxed) &
                SLOT_PAYLOAD;
            if (got < want) {
                ++violations;
            }
        }
        std::fprintf(
            stderr,
            "KVDB_PROTO lc_check: reachable=%zu violations=%llu\n",
            structural.size(),
            static_cast<unsigned long long>(violations));

    }

    // Release-cascade self-check (env KVDB_LCTEST=1, then exit). Builds a tiny
    // set of real nodes with sharing and a terminal value page, applies the real
    // inc-at-emit and gen_release logic over an in-memory store, and checks the
    // outcome against an independent reference. Scenario (ref = serial*NODE_SIZE):
    //   L1,L2,L3 = storage-flat leaves (no children); EXT = raw value page;
    //   SP = storage-page leaf -> EXT (terminal); IA = internal -> [L1,L2,SP];
    //   IB = internal -> [L1,L3]. IA and IB are version roots (metadata +1).
    // Counts after build: L1=2 (IA,IB), L2=1, L3=1, SP=1, EXT=1, IA=1, IB=1.
    // Release IA: frees IA,L2,SP,EXT; L1 drops 2->1; L3,IB untouched.
    static void lctest()
    {
        constexpr size_t NS = kv::NODE_SIZE;
        enum : uint32_t { L1 = 1, L2, L3, EXT, SP, IA, IB, NPAGES };
        std::vector<std::array<unsigned char, NS>> pages(NPAGES);
        for (auto &p : pages) {
            p.fill(0);
        }
        auto leaf = [&](uint32_t const s) {
            pages[s][0] = kv::N_LEAF_STORAGE_FLAT;
            pages[s][1] = kv::STOR_KEY;
            uint16_t const c = 1;
            std::memcpy(pages[s].data() + 2, &c, 2);
        };
        auto internal = [&](uint32_t const s, std::vector<uint32_t> const &ch) {
            pages[s][0] = kv::N_INTERNAL;
            pages[s][1] = kv::STOR_KEY;
            uint16_t const c = static_cast<uint16_t>(ch.size());
            std::memcpy(pages[s].data() + 2, &c, 2);
            unsigned char *q = pages[s].data() + kv::HDR;
            for (uint32_t const cs : ch) {
                q += kv::STOR_KEY; // dummy key
                uint64_t const r = static_cast<uint64_t>(cs) * NS;
                std::memcpy(q, &r, 8);
                q += 8;
            }
        };
        leaf(L1);
        leaf(L2);
        leaf(L3);
        // SP: storage-page leaf, one record with an out-of-line value page EXT.
        pages[SP][0] = kv::N_LEAF_STORAGE_PAGE;
        {
            uint16_t const c = 1;
            std::memcpy(pages[SP].data() + 2, &c, 2);
            uint16_t const off = 128; // record offset within the page
            std::memcpy(pages[SP].data() + kv::HDR, &off, 2);
            pages[SP][off + kv::PG_FLAG] = 1; // out-of-line
            uint64_t const ext = static_cast<uint64_t>(EXT) * NS;
            std::memcpy(pages[SP].data() + off + kv::PG_PAYLOAD, &ext, 8);
        }
        internal(IA, {L1, L2, SP});
        internal(IB, {L1, L3});

        std::vector<std::atomic<uint32_t>> slots(NPAGES); // all 0
        std::atomic<uint32_t> head{SLOT_NIL};
        auto read_into = [&](uint64_t const r, unsigned char *const dst) {
            std::memcpy(dst, pages[r / NS].data(), NS);
        };
        // Emit order (bottom-up): inc each emitted node's children, then the
        // two roots' metadata reference.
        auto emit_inc = [&](uint32_t const s) {
            for_each_child_ref(
                pages[s].data(), [&](uint64_t const c, ChildKind) {
                    slots[c / NS].fetch_add(1, std::memory_order_relaxed);
                });
        };
        emit_inc(SP); // EXT -> 1
        emit_inc(IA); // L1,L2,SP -> +1
        emit_inc(IB); // L1,L3 -> +1
        slots[IA].fetch_add(1, std::memory_order_relaxed); // metadata ref
        slots[IB].fetch_add(1, std::memory_order_relaxed);
        uint32_t const want0[NPAGES] = {0, 2, 1, 1, 1, 1, 1, 1};
        for (uint32_t s = L1; s < NPAGES; ++s) {
            MONAD_ASSERT(slots[s].load() == want0[s]);
        }

        gen_release(slots, head, read_into, static_cast<uint64_t>(IA) * NS,
                    ChildKind::Node);

        auto freed = [&](uint32_t const s) {
            return (slots[s].load() & SLOT_FREE_BIT) != 0;
        };
        MONAD_ASSERT(freed(IA) && freed(L2) && freed(SP) && freed(EXT));
        MONAD_ASSERT(!freed(L1) && slots[L1].load() == 1);
        MONAD_ASSERT(!freed(L3) && slots[L3].load() == 1);
        MONAD_ASSERT(!freed(IB) && slots[IB].load() == 1);
        // The freelist head chain holds exactly the four freed pages.
        std::unordered_set<uint32_t> onlist;
        for (uint32_t h = head.load(); h != SLOT_NIL;
             h = slots[h].load() & SLOT_PAYLOAD) {
            MONAD_ASSERT(onlist.insert(h).second); // no cycle
        }
        MONAD_ASSERT(
            (onlist == std::unordered_set<uint32_t>{IA, L2, SP, EXT}));

        // Releasing the other root frees the rest (L1 now 1 -> 0).
        gen_release(slots, head, read_into, static_cast<uint64_t>(IB) * NS,
                    ChildKind::Node);
        MONAD_ASSERT(freed(IB) && freed(L1) && freed(L3));
        std::fprintf(stderr, "KVDB_LCTEST ok: cascade + freelist verified\n");
    }

    // Hazard-array self-check (env KVDB_HZTEST=1, then exit). Exercises the
    // shared-memory pool: acquire (bump), publish, collect (exec scan), release
    // (clears HPs + frees the slot), and slot reuse via the lock-bit free list.
    static void hztest()
    {
        kv::HazardArray h;
        h.create("/kvdb_hztest");
        uint32_t const a = h.acquire(); // slot 1 (0 reserved)
        uint32_t const b = h.acquire(); // slot 2
        MONAD_ASSERT(a == 1 && b == 2);
        h.publish1(a, 0x1000);
        h.publish2(a, 0x2000);
        h.publish1(b, 0x3000);
        {
            std::unordered_set<uint64_t> s;
            h.collect(s);
            MONAD_ASSERT(
                (s == std::unordered_set<uint64_t>{0x1000, 0x2000, 0x3000}));
        }
        h.release(a); // clears slot 1's HPs, returns it to the free list
        {
            std::unordered_set<uint64_t> s;
            h.collect(s);
            MONAD_ASSERT((s == std::unordered_set<uint64_t>{0x3000}));
        }
        uint32_t const c = h.acquire(); // reuses the freed slot 1
        MONAD_ASSERT(c == a);
        h.close();
        ::shm_unlink("/kvdb_hztest");
        std::fprintf(
            stderr, "KVDB_HZTEST ok: hazard array acquire/publish/collect/"
                    "release/reuse\n");
    }

    // History window: is `block` a retained finalized block?
    bool mv_has(uint64_t const block) const
    {
        return meta_ != nullptr && block >= meta_->oldest_block &&
               block <= meta_->finalized_block;
    }

    // Position the read cursor on (parent_block, parent_id) before a commit:
    // root_ = the parent's state root, and remember parent_id for the child's
    // block map value. A finalized parent (block <= finalized) is read by block.
    void set_tip(uint64_t const parent_block, bytes32_t const &parent_id)
    {
        cur_parent_id_ = parent_id;
        if (parent_block <= meta_->finalized_block) {
            root_ = finalized_state_root(parent_block);
        }
        else {
            KvStore st{this};
            unsigned char key[BM_KL], v[BM_VL];
            bm_key(key, parent_block, parent_id);
            MONAD_ASSERT(kv::blockmap::lookup(
                st, meta_->tree_root, key, BM_KL, BM_VL, v));
            std::memcpy(&root_, v, 8);
        }
    }

    // Reassemble a blob (N_BLOB_INLINE / N_BLOB_INDEX) into `out`. NULL_REF or a
    // non-blob root -> empty. Copies out immediately (KvStore::read reuses one
    // buffer across reads).
    void read_blob(KvStore &st, uint64_t const root, byte_string &out)
    {
        out.clear();
        if (root == kv::NULL_REF) {
            return;
        }
        append_blob(st, root, out);
    }

    // Append the bytes under `root`. An index page's children are raw data
    // pages at height 0 (buf[1]) and index pages of the level below above it;
    // each level's CODE_LEN is the length of the range IT covers, so no extra
    // state is needed to know where a child's contribution ends.
    void append_blob(KvStore &st, uint64_t const root, byte_string &out)
    {
        unsigned char buf[kv::NODE_SIZE]; // copy: st.read reuses one buffer
        std::memcpy(buf, st.read(root), kv::NODE_SIZE);
        uint64_t len;
        std::memcpy(&len, buf + CODE_LEN, 8);
        if (buf[0] == kv::N_BLOB_INLINE) {
            out.append(buf + CODE_INLINE_OFF, buf + CODE_INLINE_OFF + len);
            return;
        }
        MONAD_ASSERT(buf[0] == kv::N_BLOB_INDEX);
        uint8_t const height = buf[1];
        uint32_t nc;
        std::memcpy(&nc, buf + CODE_NCHILD, 4);
        std::vector<uint64_t> refs(nc);
        std::memcpy(refs.data(), buf + CODE_CHILDREN, nc * 8);
        size_t const want = out.size() + len;
        out.reserve(want);
        for (uint32_t i = 0; i < nc && out.size() < want; ++i) {
            if (height == 0) {
                unsigned char const *const d = st.read(refs[i]);
                size_t const take =
                    std::min<size_t>(kv::NODE_SIZE, want - out.size());
                out.append(d, d + take);
            }
            else {
                append_blob(st, refs[i], out);
            }
        }
    }

    // Delete a departing block's entries from the global hash indexes: its tx
    // hashes (from the block's BLOB_TXHASHES blob) from the tx-hash index, and
    // its block hash H (32B, from the block-map leaf value) from the block-hash
    // index. A base-image block (N_INTERNAL root, no blobs, H==0) has none.
    void delete_block_indexes(
        KvStore &st, uint64_t const block_root,
        unsigned char const *const block_hash_H)
    {
        if (block_root == kv::NULL_REF) {
            return;
        }
        uint64_t txh_blob = kv::NULL_REF;
        {
            unsigned char const *const n = st.read(block_root);
            if (n[0] != kv::N_BLOCK_ROOT) {
                return; // base-image root: no blobs, no index entries
            }
            std::memcpy(
                &txh_blob,
                n + kv::BLOCK_ROOT_BLOB_OFF + kv::BLOB_TXHASHES * 8, 8);
        }
        if (txh_blob != kv::NULL_REF) {
            byte_string hashes;
            read_blob(st, txh_blob, hashes);
            for (size_t off = 0; off + 32 <= hashes.size(); off += 32) {
                install_index_root(
                    meta_->txhash_index_root,
                    kv::blockmap::unlink(
                        st, meta_->txhash_index_root, hashes.data() + off,
                        TXH_KL, TXH_VL));
            }
        }
        bool h_nonzero = false;
        for (int i = 0; i < 32; ++i) {
            if (block_hash_H[i] != 0) {
                h_nonzero = true;
                break;
            }
        }
        if (h_nonzero) {
            install_index_root(
                meta_->blockhash_index_root,
                kv::blockmap::unlink(
                    st, meta_->blockhash_index_root, block_hash_H, BLKH_KL,
                    BLKH_VL));
        }
    }

    // Finalize (block N, id X): synchronously unlink the block-N losers (its
    // siblings) so a block-keyed read is unambiguous, then advance the finalized
    // frontier. The winner stays in the block map. No node freeing here (async
    // reclamation reclaims the unlinked losers and dead subtrees later).
    // Remove block `b`'s entry from the block map and retire its state root
    // (there is one entry per finalized block; loop defends against strays).
    void prune_block(KvStore &st, uint64_t const b)
    {
        for (;;) {
            unsigned char probe[BM_KL], k[BM_KL], v[BM_VL];
            bm_key(probe, b, bytes32_t{});
            if (!kv::blockmap::lower_bound(
                    st, meta_->tree_root, probe, BM_KL, BM_VL, k, v)) {
                return;
            }
            if (bm_block(k) != b) {
                return;
            }
            uint64_t sr;
            std::memcpy(&sr, v, 8);
            delete_block_indexes(st, sr, v + BM_HASH_OFF);
            install_block_map_root(kv::blockmap::unlink(
                st, meta_->tree_root, k, BM_KL, BM_VL));
            retire_state_root(sr);
        }
    }

    void finalize_block(uint64_t const block, bytes32_t const &id)
    {
        KvStore st{this};
        unsigned char lo[BM_KL], hi[BM_KL];
        bm_key(lo, block, bytes32_t{});
        bytes32_t maxid;
        std::memset(maxid.bytes, 0xff, 32);
        bm_key(hi, block, maxid);
        // Collect the block-N losers (key != id) with their full value (state
        // root + H, for index cleanup; scan pointers are transient, so copy).
        std::vector<std::pair<
            std::array<unsigned char, BM_KL>, std::array<unsigned char, BM_VL>>>
            losers;
        uint64_t nsib = 0;
        kv::blockmap::scan_range(
            st, meta_->tree_root, lo, hi, BM_KL, BM_VL,
            [&](unsigned char const *const k, unsigned char const *const vv) {
                ++nsib;
                if (std::memcmp(k + 8, id.bytes, 32) != 0) {
                    std::array<unsigned char, BM_KL> kk;
                    std::array<unsigned char, BM_VL> vval;
                    std::memcpy(kk.data(), k, BM_KL);
                    std::memcpy(vval.data(), vv, BM_VL);
                    losers.emplace_back(kk, vval);
                }
            });
        MONAD_ASSERT(nsib >= 1); // the finalized block was committed
        for (auto const &[kk, vval] : losers) {
            uint64_t sr;
            std::memcpy(&sr, vval.data(), 8);
            delete_block_indexes(st, sr, vval.data() + BM_HASH_OFF);
            install_block_map_root(kv::blockmap::unlink(
                st, meta_->tree_root, kk.data(), BM_KL, BM_VL));
            retire_state_root(sr);
        }
        if (nsib > 1) { // a fork was resolved
            fork_commits.fetch_add(1, std::memory_order_relaxed);
            fork_finalized.fetch_add(1, std::memory_order_relaxed);
        }
        meta_->finalized_block = block;
        std::memcpy(meta_->finalized_id, id.bytes, 32);
        // Advance the window: retain at most KVDB_HISTORY_N finalized blocks
        // [oldest, finalized]. Each block that falls off is pruned (its entry
        // removed, its state root retired).
        uint64_t const want_oldest = (block + 1 > KVDB_HISTORY_N)
                                         ? (block + 1 - KVDB_HISTORY_N)
                                         : meta_->oldest_block;
        while (meta_->oldest_block < want_oldest) {
            prune_block(st, meta_->oldest_block);
            ++meta_->oldest_block;
        }
        // Reclaim retired roots (hazard-gated) every N finalizes.
        if (reclaim_every_ != 0 && block % reclaim_every_ == 0) {
            reclaim_step();
        }
        if (reclaim_log_) {
            uint64_t const bumped = write_pos_ >= image_bytes
                                        ? (write_pos_ - image_bytes) /
                                              kv::NODE_SIZE
                                        : 0;
            std::fprintf(
                stderr,
                "KVDB_PROTO __reclaim bl=%llu bump=+%llu reuse=+%llu free=+%llu "
                "retired=%zu (bumped=%llu reused=%llu)\n",
                static_cast<unsigned long long>(block),
                static_cast<unsigned long long>(bumped - prev_bumped_),
                static_cast<unsigned long long>(reused_pages_ - prev_reused_),
                static_cast<unsigned long long>(freed_pages_ - prev_freed_),
                retired_roots_.size(),
                static_cast<unsigned long long>(bumped),
                static_cast<unsigned long long>(reused_pages_));
            prev_bumped_ = bumped;
            prev_reused_ = reused_pages_;
            prev_freed_ = freed_pages_;
        }
        std::atomic_thread_fence(std::memory_order_release);
        ::msync(meta_map_, KVDB_META_BYTES, MS_ASYNC);
    }

    // Publish the consensus commit-state cursors into shared KvMeta, mirroring
    // triedb's set_latest_{proposed,voted}. Pure pointer stamps: the (block, id)
    // leaf already exists in the block map from commit; these just name the
    // canonical head. Same release-fence + msync publish as finalize_block. A
    // concurrent RPC reader validates the (block, id) pair with an id re-read
    // (block_id is a unique hash), exactly as it does against triedb.
    // Publish a (block, id) cursor pair under the seqlock: bump to odd, write,
    // bump to even. Both stores are seq_cst so they pair with the reader's
    // seq_cst loads. Exec is the only writer, so the counter needs no CAS.
    template <typename Write>
    void publish_tag(Write &&write)
    {
        uint64_t const s = meta_->tag_seq;
        __atomic_store_n(&meta_->tag_seq, s + 1, __ATOMIC_SEQ_CST);
        write();
        __atomic_store_n(&meta_->tag_seq, s + 2, __ATOMIC_SEQ_CST);
        std::atomic_thread_fence(std::memory_order_release);
        ::msync(meta_map_, KVDB_META_BYTES, MS_ASYNC);
    }

    void publish_proposed(uint64_t const block, bytes32_t const &id)
    {
        publish_tag([&] {
            meta_->proposed_block = block;
            std::memcpy(meta_->proposed_id, id.bytes, 32);
        });
    }

    void publish_voted(uint64_t const block, bytes32_t const &id)
    {
        publish_tag([&] {
            meta_->voted_block = block;
            std::memcpy(meta_->voted_id, id.bytes, 32);
        });
    }

    // Write this block's buffered new nodes to KV's device range and cache them,
    // then release the RAM buffer. Each node is submitted as a 4KB O_DIRECT write
    // on KvIo (concurrent, io_uring) at its own ref (wref_[i]) — refs may be
    // reused reclaimed pages, so they are not contiguous — then one drain.
    void write_block_nodes(MONAD_ASYNC_NAMESPACE::AsyncIO & /*io*/)
    {
        size_t const n = wbuf_.size();
        kv::KvIo &io = kvio();
        for (size_t i = 0; i < n; ++i) {
            uint64_t const ref = wref_[i];
            cache_.insert(ref, wbuf_[i]);
            io.submit_write(ref, wbuf_[i].data());
        }
        io.drain();
        wbuf_.clear();
        wbuf_.shrink_to_fit();
        wref_.clear();
        wbuf_index_.clear();
    }

    // ── item (2): async io_uring reads (run on the DB io service thread) ─
    // Deliver the native Account for `a`, or nullopt if absent. Reads from the
    // latest root; the 4-arg overload reads from an explicit (historical) root.
    void account_async(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io, Address const &a,
        std::move_only_function<void(std::optional<Account>)> done)
    {
        account_async(io, a, root_, std::move(done));
    }

    void account_async(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io, Address const &a,
        uint64_t const root,
        std::move_only_function<void(std::optional<Account>)> done)
    {
        kv::KeyBuf key{};
        std::memcpy(key.data(), a.bytes, kv::ACCT_KEY);
        kv::kv_to_leaf(
            read_ctx(io),
            root,
            key,
            [a, done = std::move(done)](
                unsigned char const *const leaf, uint32_t const depth,
                uint32_t const io_) mutable {
                std::optional<Account> acct = kv_scan_account(leaf, a);
                // account lookup: nonempty if the account exists, else empty.
                KVDB_ADD(
                    acct.has_value() ? ::monad::kvdb_metrics::kv_acct_nonempty
                                     : ::monad::kvdb_metrics::kv_acct_empty,
                    depth,
                    io_);
                done(std::move(acct));
            });
        // No drain: the submitted read(s) complete asynchronously; the io
        // service loop reaps this KvIo ring each iteration (via the registered
        // poll hook) and fires `done`, so reads from parallel fibers overlap.
    }

    // Deliver the 32B value for (a, key), or zero if absent. Reads from the
    // latest root; the 5-arg overload reads from an explicit (historical) root.
    void slot_async(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io, Address const &a,
        bytes32_t const &key, std::move_only_function<void(bytes32_t)> done)
    {
        slot_async(io, a, key, root_, std::move(done));
    }

    void slot_async(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io, Address const &a,
        bytes32_t const &key, uint64_t const root,
        std::move_only_function<void(bytes32_t)> done)
    {
        kv::Ctx const c = read_ctx(io);
        kv::KeyBuf akey{};
        std::memcpy(akey.data(), a.bytes, kv::ACCT_KEY);
        // A storage lookup traverses the account tree (to the storage-root)
        // then the storage subtree; both descents' depth and io sum into the
        // per-lookup total that kv_deliver_slot records (zero vs nonzero slot).
        kv::kv_to_leaf(
            c,
            root,
            akey,
            [c, a, key, done = std::move(done)](
                unsigned char const *const acct_leaf, uint32_t const dacct,
                uint32_t const iacct) mutable {
                std::optional<uint64_t> const sref =
                    kv_scan_sref(acct_leaf, a);
                if (!sref.has_value()) {
                    // no account / no storage subtree: zero, cost = account
                    // descent only.
                    KVDB_ADD(
                        ::monad::kvdb_metrics::kv_stor_zero, dacct, iacct);
                    done(bytes32_t{});
                    return;
                }
                kv::KeyBuf skey{};
                std::memcpy(skey.data(), key.bytes, kv::STOR_KEY);
                kv::kv_to_leaf(
                    c,
                    *sref,
                    skey,
                    [c, key, done = std::move(done)](
                        unsigned char const *const sleaf, uint32_t const dtot,
                        uint32_t const itot) mutable {
                        kv_deliver_slot(
                            c, sleaf, key, dtot, itot, std::move(done));
                    },
                    dacct + 1, // continue depth from the account descent
                    iacct);
            });
        // No drain: reaped asynchronously by the io loop's poll hook (see
        // account_async), so storage reads from parallel fibers overlap.
    }

    // Async prefetch (item 2): before the synchronous build, warm the node
    // cache for every updated key's ancestry path, so merge_acct/merge_stor hit
    // cache instead of the NodeReader's fallback ::pread. Issues concurrent
    // io_uring descents (each account path, then that account's storage paths
    // via its sref), then one drain (storage reads issued from the account
    // continuations are drained transitively). merge_acct/merge_stor read
    // exactly these paths (partial COW; untouched subtrees shared by ref), so
    // this covers the whole construct read set. Runs on the io thread.
    void prefetch_updates(
        MONAD_ASYNC_NAMESPACE::AsyncIO &io,
        std::vector<kv::AccountUpdates> const &ups)
    {
        kv::Ctx const c = read_ctx(io);
        kvio().in_batch = true; // exclude the fan-out batch from serve metrics
        for (auto const &au : ups) {
            kv::KeyBuf akey{};
            std::memcpy(akey.data(), au.addr.bytes, kv::ACCT_KEY);
            Address const addr = au.addr;
            // ups outlives the drain below, so a pointer into it is stable.
            std::vector<kv::SlotUpdate> const *const slots = &au.slots;
            kv::kv_to_leaf(
                c,
                root_,
                akey,
                [c, addr, slots](
                    unsigned char const *const acct_leaf, uint32_t const depth,
                    uint32_t const io_) {
                    KVDB_ADD(::monad::kvdb_metrics::kv_prefetch, depth, io_);
                    std::optional<uint64_t> const sref =
                        kv_scan_sref(acct_leaf, addr);
                    if (!sref.has_value()) {
                        return; // no storage subtree to prefetch
                    }
                    for (auto const &s : *slots) {
                        kv::KeyBuf skey{};
                        std::memcpy(skey.data(), s.slot.bytes, kv::STOR_KEY);
                        kv::kv_to_leaf(
                            c,
                            *sref,
                            skey,
                            [](unsigned char const *, uint32_t const d,
                               uint32_t const i) {
                                KVDB_ADD(
                                    ::monad::kvdb_metrics::kv_prefetch, d, i);
                            });
                    }
                });
        }
        kvio().drain(); // drain account + storage prefetch descents
        kvio().in_batch = false;
    }

private:
    // Scan a LEAF_ACCOUNT node for `a`'s native Account.
    static std::optional<Account>
    kv_scan_account(unsigned char const *const leaf, Address const &a)
    {
        uint16_t count;
        std::memcpy(&count, leaf + 2, sizeof(count));
        unsigned char const *const p = leaf + kv::HDR;
        for (size_t i = 0; i < count; ++i) {
            unsigned char const *const rec = p + i * kv::ACCT_REC;
            if (std::memcmp(rec, a.bytes, kv::ACCT_KEY) == 0) {
                Account acct;
                std::memcpy(&acct, rec + kv::ACCT_KEY, sizeof(Account));
                return acct;
            }
        }
        return std::nullopt;
    }

    // Scan a LEAF_ACCOUNT node for `a`'s storage root (nullopt if no account
    // or the account has no storage subtree).
    static std::optional<uint64_t>
    kv_scan_sref(unsigned char const *const leaf, Address const &a)
    {
        uint16_t count;
        std::memcpy(&count, leaf + 2, sizeof(count));
        unsigned char const *const p = leaf + kv::HDR;
        for (size_t i = 0; i < count; ++i) {
            unsigned char const *const rec = p + i * kv::ACCT_REC;
            if (std::memcmp(rec, a.bytes, kv::ACCT_KEY) == 0) {
                uint64_t sref;
                std::memcpy(&sref, rec + kv::ACCT_KEY + sizeof(Account), 8);
                if (sref == kv::NULL_REF) {
                    return std::nullopt;
                }
                return sref;
            }
        }
        return std::nullopt;
    }

    // Extract the slot value from a storage leaf (flat or page). The page
    // extension case needs one more node fetch, hence the continuation form.
    static void kv_deliver_slot(
        kv::Ctx const c, unsigned char const *const leaf, bytes32_t const key,
        uint32_t const depth, uint32_t const io,
        std::move_only_function<void(bytes32_t)> done)
    {
        // depth/io = per-lookup totals to this storage leaf (account descent +
        // storage descent). Recorded on kv_stor_nonzero (value present) or
        // kv_stor_zero (absent) so both populations are measured.
        uint16_t count;
        std::memcpy(&count, leaf + 2, sizeof(count));
        unsigned char const *const p = leaf + kv::HDR;
        if (leaf[0] == kv::N_LEAF_STORAGE_FLAT) {
            for (size_t i = 0; i < count; ++i) {
                unsigned char const *const rec = p + i * kv::STOR_REC_FLAT;
                if (std::memcmp(rec, key.bytes, kv::STOR_KEY) == 0) {
                    bytes32_t out{};
                    std::memcpy(out.bytes, rec + 32, 32);
                    KVDB_ADD(
                        ::monad::kvdb_metrics::kv_stor_nonzero, depth, io);
                    done(out);
                    return;
                }
            }
            KVDB_ADD(::monad::kvdb_metrics::kv_stor_zero, depth, io);
            done(bytes32_t{});
            return;
        }
        // page leaf: locate the page record for key's page_base
        bytes32_t base_key = key;
        base_key.bytes[31] =
            static_cast<unsigned char>(base_key.bytes[31] & 0x80);
        size_t const idx = static_cast<size_t>(key.bytes[31] & 0x7f);
        for (size_t i = 0; i < count; ++i) {
            uint16_t off;
            std::memcpy(&off, p + i * 2, sizeof(off));
            unsigned char const *const rec = leaf + off;
            if (std::memcmp(rec, base_key.bytes, kv::STOR_KEY) != 0) {
                continue;
            }
            unsigned char const *const bm = rec + kv::PG_BITMAP;
            if (!kv::bit_test(bm, idx)) {
                KVDB_ADD(::monad::kvdb_metrics::kv_stor_zero, depth, io);
                done(bytes32_t{}); // slot not present
                return;
            }
            size_t const rank = kv::bit_rank(bm, idx);
            if (rec[kv::PG_FLAG] == 0) {
                bytes32_t out{};
                std::memcpy(out.bytes, rec + kv::PG_PAYLOAD + rank * 32, 32);
                KVDB_ADD(::monad::kvdb_metrics::kv_stor_nonzero, depth, io);
                done(out);
                return;
            }
            // extension node holds the values; one more fetch (+1 depth)
            uint64_t ext_ref;
            std::memcpy(&ext_ref, rec + kv::PG_PAYLOAD, sizeof(ext_ref));
            kv::kv_read_node(
                c,
                ext_ref,
                [rank, depth, io, done = std::move(done)](
                    unsigned char const *const ext, bool const was_io) mutable {
                    KVDB_ADD(
                        ::monad::kvdb_metrics::kv_stor_nonzero,
                        depth + 1,
                        io + (was_io ? 1u : 0u));
                    bytes32_t out{};
                    std::memcpy(out.bytes, ext + rank * 32, 32);
                    done(out);
                });
            return;
        }
        KVDB_ADD(::monad::kvdb_metrics::kv_stor_zero, depth, io);
        done(bytes32_t{}); // page not present
    }
};
#endif

TrieDb::TrieDb(mpt::Db &db, bool const enable_multiblock_cache)
    : db_{db}
    , block_number_{db.get_latest_finalized_version()}
    , proposal_block_id_{bytes32_t{}}
    , prefix_{finalized_nibbles}
    , curr_root_{db.load_root_for_version(block_number_)}
    , cache_{enable_multiblock_cache ? std::make_unique<DbCache>() : nullptr}
    , page_encoded_{db_.state_machine_type() == mpt::state_machine_kind::monad}
{
#if KVDB_PROTO
    if (std::getenv("KVDB_BMTEST")) { // validation: block map self-check, then exit
        kv::bmtest();
        std::exit(0);
    }
    if (std::getenv("KVDB_LCTEST")) { // validation: release-cascade self-check
        KvShadow::lctest();
        std::exit(0);
    }
    if (char const *const rd = std::getenv("KVDB_RDTEST");
        rd != nullptr && std::strcmp(rd, "1") == 0) {
        kv_rd_check_ = true; // drive a KvReader per block (see kv_reader_validate)
    }
    if (char const *const s = std::getenv("KVDB_RDHOLD")) {
        kv_hold_n_ = std::strtoull(s, nullptr, 10);
    }
    if (std::getenv("KVDB_HZTEST")) { // validation: hazard-array self-check
        KvShadow::hztest();
        std::exit(0);
    }
    if (char const *const img = std::getenv("KVDB_IMAGE")) {
        kv_ = std::make_unique<KvShadow>(img);
        std::fprintf(
            stderr,
            "KVDB_PROTO: shadow image loaded: %s (format=%s, accounts=%lu, "
            "slots=%lu)\n",
            img,
            kv_->hdr.storage_format ? "pages" : "flat",
            kv_->hdr.num_accounts,
            kv_->hdr.num_slots);
        // Validation (env KVDB_TAGTEST=<seconds>): race the tag-cursor bracket
        // directly, which no replay can do -- exec stamps the cursors on its
        // own commit path, so a reader driven from there is sequential with the
        // writer and the bracket never re-reads. Here a writer thread publishes
        // while this thread reads, both flat out, on the same meta page (exec
        // maps it RW via kv_, the reader RO).
        //
        // The pairs are self-describing: every id is four lanes of its own block
        // number, so a torn pair is DETECTABLE rather than merely possible --
        // the reader asserts id == f(block) on whatever it accepted. That is
        // what makes this a test of the bracket rejecting tearing, and not just
        // a count of how often it retried.
        if (std::getenv("KVDB_PGTALLY")) { // read-only storage-page census
            kv_->pgtally();
            std::exit(0);
        }
        if (char const *const pt = std::getenv("KVDB_PGTEST")) {
            pgtest(std::strtoull(pt, nullptr, 10));
            std::exit(0);
        }
        if (char const *const tt = std::getenv("KVDB_TAGTEST")) {
            tagtest(std::strtoull(tt, nullptr, 10));
            std::exit(0);
        }
        // Have the io service loop reap KV's own io_uring ring each iteration,
        // so KV reads pipeline across the parallel exec fibers (submit-and-
        // return, no per-lookup drain). Runs on the io thread; guards on
        // kvio_ptr() (null until the first KV io lazily builds the engine).
        db_.set_kv_poll_hook([this]() -> bool {
            if (kv_ != nullptr) {
                if (kv::KvIo *const k = kv_->kvio_ptr()) {
                    k->reap_ready();
                    return k->outstanding() > 0;
                }
            }
            return false;
        });
    }
#endif
}

TrieDb::~TrieDb()
{
#if KVDB_PROTO
    if (kv_rd_ != nullptr) { // KVDB_RDTEST reader (detaches shm + mappings)
        kv_reader_close(kv_rd_);
        kv_rd_ = nullptr;
    }
#endif
#if KVDB_PROTO
    if (kv_) {
        // Stop the io service loop from calling the poll hook (which touches
        // kv_) and wait until it has, before we tear down KV state below.
        db_.clear_kv_poll_hook();
        std::fprintf(
            stderr,
            "KVDB_PROTO shadow totals: acc[checked=%lu mismatch=%lu] "
            "sto[checked=%lu mismatch=%lu]\n",
            kv_->acc_checked.load(std::memory_order_relaxed),
            kv_->acc_mismatch.load(std::memory_order_relaxed),
            kv_->sto_checked.load(std::memory_order_relaxed),
            kv_->sto_mismatch.load(std::memory_order_relaxed));
        // kvdb_base multiversion: historical-read validation totals (KV ring
        // root at block T-D vs triedb at version T-D), and skips where T-D fell
        // outside the KV or triedb window.
        std::fprintf(
            stderr,
            "KVDB_PROTO mv totals: acc[checked=%lu mismatch=%lu] "
            "sto[checked=%lu mismatch=%lu] skipped=%lu\n",
            kv_->mv_acc_checked.load(std::memory_order_relaxed),
            kv_->mv_acc_mismatch.load(std::memory_order_relaxed),
            kv_->mv_sto_checked.load(std::memory_order_relaxed),
            kv_->mv_sto_mismatch.load(std::memory_order_relaxed),
            kv_->mv_skipped.load(std::memory_order_relaxed));
        std::fprintf(
            stderr,
            "KVDB_PROTO up totals: acc[checked=%lu mismatch=%lu] "
            "sto[checked=%lu mismatch=%lu]\n",
            kv_->up_acc_checked.load(std::memory_order_relaxed),
            kv_->up_acc_mismatch.load(std::memory_order_relaxed),
            kv_->up_sto_checked.load(std::memory_order_relaxed),
            kv_->up_sto_mismatch.load(std::memory_order_relaxed));
        // Sibling-fork structural totals (KVDB_SIBLING_EVERY). Zero here with the
        // knob on means no fork was actually created/resolved (a silent no-op).
        std::fprintf(
            stderr,
            "KVDB_PROTO fork totals: commits=%lu finalized=%lu\n",
            kv_->fork_commits.load(std::memory_order_relaxed),
            kv_->fork_finalized.load(std::memory_order_relaxed));
        std::fprintf(
            stderr,
            "KVDB_PROTO code totals: checked=%lu mismatch=%lu\n",
            kv_->code_checked.load(std::memory_order_relaxed),
            kv_->code_mismatch.load(std::memory_order_relaxed));
        // RPC read-side totals (KVDB_RDTEST). All-zero when the knob is off.
        std::fprintf(
            stderr,
            "KVDB_PROTO rd totals: pins=%lu pin_fail=%lu "
            "acc[checked=%lu mismatch=%lu] sto[checked=%lu mismatch=%lu] "
            "code[checked=%lu mismatch=%lu] blob[checked=%lu mismatch=%lu] "
            "index[checked=%lu mismatch=%lu]\n",
            kv_->rd_pins.load(std::memory_order_relaxed),
            kv_->rd_pin_fail.load(std::memory_order_relaxed),
            kv_->rd_acc_checked.load(std::memory_order_relaxed),
            kv_->rd_acc_mismatch.load(std::memory_order_relaxed),
            kv_->rd_sto_checked.load(std::memory_order_relaxed),
            kv_->rd_sto_mismatch.load(std::memory_order_relaxed),
            kv_->rd_code_checked.load(std::memory_order_relaxed),
            kv_->rd_code_mismatch.load(std::memory_order_relaxed),
            kv_->rd_blob_checked.load(std::memory_order_relaxed),
            kv_->rd_blob_mismatch.load(std::memory_order_relaxed),
            kv_->rd_index_checked.load(std::memory_order_relaxed),
            kv_->rd_index_mismatch.load(std::memory_order_relaxed));
        std::fprintf(
            stderr,
            "KVDB_PROTO rd hold: blocks=%lu checked=%lu mismatch=%lu\n",
            kv_->rd_hold_blocks.load(std::memory_order_relaxed),
            kv_->rd_hold_checked.load(std::memory_order_relaxed),
            kv_->rd_hold_mismatch.load(std::memory_order_relaxed));
        std::fprintf(
            stderr,
            "KVDB_PROTO rd tx: checked=%lu mismatch=%lu | pruned_pin "
            "checked=%lu mismatch=%lu | proposal_pin checked=%lu "
            "mismatch=%lu\n",
            kv_->rd_tx_checked.load(std::memory_order_relaxed),
            kv_->rd_tx_mismatch.load(std::memory_order_relaxed),
            kv_->rd_pruned_checked.load(std::memory_order_relaxed),
            kv_->rd_pruned_mismatch.load(std::memory_order_relaxed),
            kv_->rd_prop_checked.load(std::memory_order_relaxed),
            kv_->rd_prop_mismatch.load(std::memory_order_relaxed));
        std::fprintf(
            stderr,
            "KVDB_PROTO rd tags: checked=%lu mismatch=%lu retries=%lu\n",
            kv_->rd_tag_checked.load(std::memory_order_relaxed),
            kv_->rd_tag_mismatch.load(std::memory_order_relaxed),
            kv_->rd_tag_retries.load(std::memory_order_relaxed));
        std::fprintf(
            stderr,
            "KVDB_PROTO code parallel: multipage_reads=%lu parallel_io=%lu "
            "(avg fan-out %.1f data pages/multipage read)\n",
            kv_->code_multipage_reads.load(std::memory_order_relaxed),
            kv_->code_parallel_io.load(std::memory_order_relaxed),
            kv_->code_multipage_reads.load(std::memory_order_relaxed)
                ? static_cast<double>(
                      kv_->code_parallel_io.load(std::memory_order_relaxed)) /
                      static_cast<double>(kv_->code_multipage_reads.load(
                          std::memory_order_relaxed))
                : 0.0);
        // kvdb_base: append growth over the run = retained-history cost.
        // write_pos_ starts at image_bytes and grows by each block's new nodes.
        {
            uint64_t const appended =
                kv_->write_pos_ >= kv_->image_bytes
                    ? kv_->write_pos_ - kv_->image_bytes
                    : 0;
            uint64_t const blocks = kv_->blocks_committed_;
            std::fprintf(
                stderr,
                "KVDB_PROTO append: blocks=%lu appended_bytes=%lu "
                "avg_per_block=%lu nodes_per_block=%.1f\n",
                blocks,
                appended,
                blocks ? appended / blocks : 0,
                blocks ? double(appended) / double(kv::NODE_SIZE) / double(blocks)
                       : 0.0);
        }
    #if KVDB_METRICS
        if (kv::KvIo const *const k = kv_->kvio_ptr()) {
            std::fprintf(
                stderr,
                "KVDB_PROTO kv_read_pipeline: max_read_in_flight=%zu "
                "reads_submitted=%lu reads_overlapped=%lu\n",
                k->max_read_in_flight,
                k->reads_submitted,
                k->reads_overlapped);
        }
        // Execution read-path node reads per lookup type, trie db vs kv db.
        // RAW counters only; derived metrics (avg depth = depth_sum/reads, node
        // cache hit rate = hits/(hits+io), account/storage/combined and
        // value/no-value roll-ups, trie/kv ratios) are computed after the fact by
        // scripts/derive_read_metrics.py, so changing what we derive never needs
        // a rerun. Every lookup is counted, partitioned found vs not-found (empty
        // account / zero storage) so no traversal is dropped. Raw fields:
        //   reads     = lookups in this bucket
        //   depth_sum = sum of per-lookup total depths (avg = depth_sum/reads)
        //   max_depth = deepest lookup (nodes to the value)
        //   hits/io   = node cache hits / device reads over the traversed nodes
        // kv storage depth = account-tree descent + storage-subtree descent
        // summed. trie_code isolates read_code; trie_other = untagged finds;
        // kv_prefetch = commit-path warm reads.
        auto const ld = [](std::atomic<uint64_t> const &a) {
            return a.load(std::memory_order_relaxed);
        };
        auto const line = [&ld](char const *const name,
                                ::monad::kvdb_metrics::ReadCounters const &b) {
            std::fprintf(
                stderr,
                "KVDB_PROTO %-18s reads=%lu depth_sum=%lu max_depth=%u "
                "hits=%lu io=%lu\n",
                name,
                ld(b.reads),
                ld(b.depth_sum),
                b.max_depth.load(std::memory_order_relaxed),
                ld(b.hits),
                ld(b.io_reads));
        };
        line("trie_acct_empty", ::monad::kvdb_metrics::trie_acct_empty);
        line("trie_acct_nonempty", ::monad::kvdb_metrics::trie_acct_nonempty);
        line("kv_acct_empty", ::monad::kvdb_metrics::kv_acct_empty);
        line("kv_acct_nonempty", ::monad::kvdb_metrics::kv_acct_nonempty);
        line("trie_stor_zero", ::monad::kvdb_metrics::trie_stor_zero);
        line("trie_stor_nonzero", ::monad::kvdb_metrics::trie_stor_nonzero);
        line("kv_stor_zero", ::monad::kvdb_metrics::kv_stor_zero);
        line("kv_stor_nonzero", ::monad::kvdb_metrics::kv_stor_nonzero);
        line("trie_code", ::monad::kvdb_metrics::trie_code);
        line("kv_code", ::monad::kvdb_metrics::kv_code);
        line("trie_other", ::monad::kvdb_metrics::trie_other);
        line("kv_prefetch", ::monad::kvdb_metrics::kv_prefetch);
    #endif
    }
#endif
}

void TrieDb::reset_root(Node::SharedPtr root, uint64_t const block_number)
{
    curr_root_ = std::move(root);
    block_number_ = block_number;
}

Node::SharedPtr const &TrieDb::get_root() const
{
    return curr_root_;
}

std::optional<Account> TrieDb::read_account(Address const &addr)
{
    std::optional<Account> result;
    if (cache_ && cache_->try_read_account(addr, result)) {
        return result;
    }
#if KVDB_PROTO
    if (kv_serves()) {
        return kv_read_account(addr); // KV serves the read (perf mode)
    }
    // Tag the trie find as an account lookup (routes its node reads to trie_acct).
    ::monad::kvdb_metrics::find_kind = ::monad::kvdb_metrics::LookupKind::acct;
#endif
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
        block_number_);
    if (res.has_error()) {
        stats_account_no_value();
    }
    else {
        stats_account_value();
        auto encoded_account = res.value().node->value();
        result = decode_account_db_ignore_address(encoded_account).value();
    }
#if KVDB_PROTO
    kv_shadow_account(addr, result);
#endif
    return result;
}

bytes32_t TrieDb::read_storage(
    Address const &addr, Incarnation const incarnation, bytes32_t const &key)
{
    bytes32_t const lookup_key = storage_lookup_key(key);
    uint8_t const lookup_offset = page_encoded_ ? compute_slot_offset(key) : 0;
    bytes32_t result{};
    if (cache_ && cache_->try_read_storage(
                      addr, incarnation, lookup_key, lookup_offset, result)) {
        return result;
    }
#if KVDB_PROTO
    if (kv_serves()) {
        return kv_read_storage(addr, key); // KV serves the read (perf mode)
    }
    // Tag the trie find as a storage lookup (routes its node reads to trie_stor).
    ::monad::kvdb_metrics::find_kind = ::monad::kvdb_metrics::LookupKind::stor;
#endif
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{
                keccak256({lookup_key.bytes, sizeof(lookup_key.bytes)})}),
        block_number_);
    if (res.has_error()) {
        stats_storage_no_value();
    }
    else {
        stats_storage_value();
        auto encoded_storage = res.value().node->value();
        auto const value = decode_storage_db_ignore_key(encoded_storage);
        MONAD_ASSERT(!value.has_error());
        if (page_encoded_) {
            auto const page = decode_storage_page(value.value());
            MONAD_ASSERT(!page.has_error());
            result = page.value()[lookup_offset];
        }
        else {
            result = to_bytes(value.value());
        }
    }
#if KVDB_PROTO
    kv_shadow_storage(addr, key, result);
#endif
    return result;
}

#if KVDB_PROTO
bool TrieDb::kv_serves() const
{
    return kv_ && !kv_->shadow_;
}

// Blocking KV account read via the production io_uring path: post the KV
// descent to the DB io service thread, suspend the exec fiber on a promise.
std::optional<Account> TrieDb::kv_read_account(Address const &addr)
{
    ::boost::fibers::promise<std::optional<Account>> promise;
    auto fut = promise.get_future();
    db_.post_to_io_thread(
        [this, addr, p = std::move(promise)](
            MONAD_ASYNC_NAMESPACE::AsyncIO &io) mutable {
            kv_->account_async(
                io, addr, [p = std::move(p)](std::optional<Account> a) mutable {
                    p.set_value(std::move(a));
                });
        });
    return fut.get();
}

bytes32_t
TrieDb::kv_read_storage(Address const &addr, bytes32_t const &key)
{
    ::boost::fibers::promise<bytes32_t> promise;
    auto fut = promise.get_future();
    db_.post_to_io_thread(
        [this, addr, key, p = std::move(promise)](
            MONAD_ASYNC_NAMESPACE::AsyncIO &io) mutable {
            kv_->slot_async(
                io, addr, key,
                [p = std::move(p)](bytes32_t v) mutable { p.set_value(v); });
        });
    return fut.get();
}

// Testing-only: read from KV and compare to the triedb result.
void TrieDb::kv_shadow_account(
    Address const &addr, std::optional<Account> const &td)
{
    if (!kv_) {
        return;
    }
    kv_->acc_checked.fetch_add(1, std::memory_order_relaxed);
    std::optional<Account> const kv_acct = kv_read_account(addr);
    bool ok;
    if (kv_acct.has_value() != td.has_value()) {
        ok = false;
    }
    else if (kv_acct.has_value()) {
        ok = std::memcmp(&kv_acct.value(), &td.value(), sizeof(Account)) == 0;
    }
    else {
        ok = true;
    }
    if (!ok) {
        kv_->acc_mismatch.fetch_add(1, std::memory_order_relaxed);
    }
}

void TrieDb::kv_shadow_storage(
    Address const &addr, bytes32_t const &key, bytes32_t const &value)
{
    if (!kv_) {
        return;
    }
    kv_->sto_checked.fetch_add(1, std::memory_order_relaxed);
    bytes32_t const kv_val = kv_read_storage(addr, key);
    // triedb absent slot => value is zero; KV absent => kv_val is zero => match.
    if (std::memcmp(kv_val.bytes, value.bytes, 32) != 0) {
        kv_->sto_mismatch.fetch_add(1, std::memory_order_relaxed);
    }
}

// KV historical reads: descend from an explicit (past-block) ring root, via the
// same io_uring path as the latest-root reads. Validation only.
std::optional<Account>
TrieDb::kv_read_account_at(Address const &addr, uint64_t const root)
{
    ::boost::fibers::promise<std::optional<Account>> promise;
    auto fut = promise.get_future();
    db_.post_to_io_thread(
        [this, addr, root, p = std::move(promise)](
            MONAD_ASYNC_NAMESPACE::AsyncIO &io) mutable {
            kv_->account_async(
                io, addr, root,
                [p = std::move(p)](std::optional<Account> a) mutable {
                    p.set_value(std::move(a));
                });
        });
    return fut.get();
}

bytes32_t TrieDb::kv_read_storage_at(
    Address const &addr, bytes32_t const &key, uint64_t const root)
{
    ::boost::fibers::promise<bytes32_t> promise;
    auto fut = promise.get_future();
    db_.post_to_io_thread(
        [this, addr, key, root, p = std::move(promise)](
            MONAD_ASYNC_NAMESPACE::AsyncIO &io) mutable {
            kv_->slot_async(
                io, addr, key, root,
                [p = std::move(p)](bytes32_t v) mutable { p.set_value(v); });
        });
    return fut.get();
}

// triedb historical reads (the oracle): mirror read_account / read_storage but
// against an explicit loaded root at version K.
std::optional<Account> TrieDb::td_read_account_at(
    Node::SharedPtr const &root, uint64_t const version, Address const &addr,
    mpt::Nibbles const &top)
{
    // `top` is finalized_nibbles for a finalized block, or proposal_prefix(id)
    // for an open proposal (the subtrie the version's state lives under).
    auto const res = db_.find(
        root,
        concat(
            top,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
        version);
    if (res.has_error()) {
        return std::nullopt;
    }
    auto encoded_account = res.value().node->value();
    return decode_account_db_ignore_address(encoded_account).value();
}

bytes32_t TrieDb::td_read_storage_at(
    Node::SharedPtr const &root, uint64_t const version, Address const &addr,
    bytes32_t const &key, mpt::Nibbles const &top)
{
    bytes32_t const lookup_key = storage_lookup_key(key);
    uint8_t const lookup_offset = page_encoded_ ? compute_slot_offset(key) : 0;
    auto const res = db_.find(
        root,
        concat(
            top,
            STATE_NIBBLE,
            NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
            NibblesView{
                keccak256({lookup_key.bytes, sizeof(lookup_key.bytes)})}),
        version);
    if (res.has_error()) {
        return {};
    }
    auto encoded_storage = res.value().node->value();
    auto const value = decode_storage_db_ignore_key(encoded_storage);
    MONAD_ASSERT(!value.has_error());
    if (page_encoded_) {
        auto const page = decode_storage_page(value.value());
        MONAD_ASSERT(!page.has_error());
        return page.value()[lookup_offset];
    }
    return to_bytes(value.value());
}

// Multiversion validation: at each committed block T, for a couple of lags D,
// read a sample of this block's touched keys at block K=T-D from BOTH the KV
// ring root and triedb at version K, and compare. Both windows must contain K
// (partition: count skips, never silently drop). Proves the ring's historical
// entries resolve to correct past state, not just that they are written.
// Validation (env KVDB_PGTEST=<pages>): read slots that live in storage pages
// whose values are stored OUT OF LINE, through the RPC reader, and compare
// against triedb. Those pages hold 127-128 populated slots -- 0.03% of records
// -- so no sampled read reaches them; the pages have to be located and fed in
// deliberately, which is what this does.
void TrieDb::pgtest(size_t const want)
{
    MONAD_ASSERT(kv_ != nullptr);
    auto const pairs = kv_->find_ext_page_slots(want);
    if (pairs.empty()) {
        std::fprintf(
            stderr, "KVDB_PGTEST: no out-of-line storage page found\n");
        return;
    }
    char const *const img = std::getenv("KVDB_IMAGE");
    KvReader *const rd = (img != nullptr) ? kv_reader_open(img) : nullptr;
    MONAD_ASSERT(rd != nullptr);
    uint64_t const f = kv_reader_cursor(rd, /*finalized*/ 0);
    int64_t const h = kv_reader_protect_block(rd, f, nullptr);
    MONAD_ASSERT(h >= 0);

    // triedb at the same version is the oracle, so the comparison does not
    // reuse the rank arithmetic it is meant to check.
    Node::SharedPtr const troot = db_.load_root_for_version(f);
    uint64_t checked = 0, mismatch = 0, nonzero = 0;
    for (auto const &[addr, slot] : pairs) {
        unsigned char v[32];
        kv_reader_storage(rd, h, addr.bytes, slot.bytes, v);
        bytes32_t const td =
            td_read_storage_at(troot, f, addr, slot, finalized_nibbles);
        ++checked;
        if (std::memcmp(v, td.bytes, 32) != 0) {
            ++mismatch;
        }
        if (std::memcmp(td.bytes, bytes32_t{}.bytes, 32) != 0) {
            ++nonzero;
        }
    }
    kv_reader_end_protect(rd, h);
    kv_reader_close(rd);
    std::fprintf(
        stderr,
        "KVDB_PGTEST: pages=%zu slots checked=%llu mismatch=%llu nonzero=%llu\n",
        want,
        static_cast<unsigned long long>(checked),
        static_cast<unsigned long long>(mismatch),
        static_cast<unsigned long long>(nonzero));
    MONAD_ASSERT(mismatch == 0);
    // Every slot came from a set bit, so a zero here would mean the read went
    // somewhere else entirely -- the check would pass on two wrong answers.
    MONAD_ASSERT(nonzero == checked);
}

// Race the tag-cursor bracket for `secs` seconds. See the call site for why
// this cannot be done from the commit path.
void TrieDb::tagtest(uint64_t const secs)
{
    char const *const img = std::getenv("KVDB_IMAGE");
    KvReader *const rd = (img != nullptr) ? kv_reader_open(img) : nullptr;
    MONAD_ASSERT(rd != nullptr);

    // id = four lanes of the block number, so a pair is self-checking.
    auto const make_id = [](uint64_t const block) {
        bytes32_t id{};
        for (int lane = 0; lane < 4; ++lane) {
            std::memcpy(id.bytes + lane * 8, &block, 8);
        }
        return id;
    };
    auto const lanes_match = [](unsigned char const *const id,
                                uint64_t const block) {
        for (int lane = 0; lane < 4; ++lane) {
            uint64_t got = 0;
            std::memcpy(&got, id + lane * 8, 8);
            if (got != block) {
                return false;
            }
        }
        return true;
    };

    std::atomic<bool> stop{false};
    std::atomic<uint64_t> writes{0};
    std::thread writer{[&] {
        for (uint64_t b = 1; !stop.load(std::memory_order_relaxed); ++b) {
            bytes32_t const id = make_id(b);
            kv_->publish_proposed(b, id);
            kv_->publish_voted(b, id);
            writes.fetch_add(2, std::memory_order_relaxed);
        }
    }};

    uint64_t reads = 0, torn = 0, failed = 0;
    auto const begin = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - begin <
           std::chrono::seconds(secs)) {
        for (int i = 0; i < 1024; ++i) {
            uint64_t f = 0, e = 0, p = 0, v = 0;
            unsigned char pid[32], vid[32];
            ++reads;
            if (!kv_reader_tags(rd, &f, &e, &p, pid, &v, vid)) {
                ++failed; // gave up after its retry budget
                continue;
            }
            // Any pair the bracket accepted must be one the writer published
            // as a unit.
            if (!lanes_match(pid, p) || !lanes_match(vid, v)) {
                ++torn;
            }
        }
    }
    stop.store(true, std::memory_order_relaxed);
    writer.join();

    uint64_t const retries = kv_reader_tag_retries(rd);
    std::fprintf(
        stderr,
        "KVDB_PROTO tagtest: secs=%lu writes=%lu reads=%lu retries=%lu "
        "torn=%lu gave_up=%lu\n",
        secs,
        writes.load(std::memory_order_relaxed),
        reads,
        retries,
        torn,
        failed);
    MONAD_ASSERT(torn == 0); // a torn pair was accepted: the bracket is broken
    // Zero retries means the race never landed, so this run proved nothing
    // about the retry path -- say so rather than reporting a pass.
    if (retries == 0) {
        std::fprintf(
            stderr,
            "KVDB_PROTO tagtest: NOT EXERCISED (no retry fired; raise "
            "KVDB_TAGTEST)\n");
    }
    kv_reader_close(rd);
}

void TrieDb::kv_reader_validate(
    uint64_t const block, bytes32_t const &block_id,
    std::vector<std::pair<Address, std::optional<bytes32_t>>> const &sample)
{
    if (kv_ == nullptr || kv_rd_off_ || sample.empty()) {
        return;
    }
    if (kv_rd_ == nullptr) { // open once, on the live store exec is writing
        char const *const img = std::getenv("KVDB_IMAGE");
        kv_rd_ = (img != nullptr) ? kv_reader_open(img) : nullptr;
        if (kv_rd_ == nullptr) {
            kv_rd_off_ = true; // exec not up / bad header: don't retry
            std::fprintf(stderr, "KVDB_RDTEST: reader open failed\n");
            return;
        }
    }
    // Tag snapshot vs triedb's own cursors. Read repeatedly: exec is stamping
    // these on the commit path while we read, so a tight loop is what gives the
    // bracket's re-read a chance to fire (rd_tag_retries says whether it did).
    {
        for (int i = 0; i < 64; ++i) {
            uint64_t kf = 0, ke = 0, kp = 0, kv2 = 0;
            unsigned char pid[32], vid[32];
            kv_->rd_tag_checked.fetch_add(1, std::memory_order_relaxed);
            if (!kv_reader_tags(kv_rd_, &kf, &ke, &kp, pid, &kv2, vid)) {
                kv_->rd_tag_mismatch.fetch_add(1, std::memory_order_relaxed);
                continue;
            }
            // Each pair must be one triedb actually published. Exec advances
            // between our read and this comparison, so a pair naming a LATER
            // block than triedb's current cursor is stale-by-a-step, not wrong;
            // only an id mismatch at the SAME block is a real disagreement.
            if (kp == db_.get_latest_proposed_version() &&
                std::memcmp(
                    pid, db_.get_latest_proposed_block_id().bytes, 32) != 0) {
                kv_->rd_tag_mismatch.fetch_add(1, std::memory_order_relaxed);
            }
            if (kv2 == db_.get_latest_voted_version() &&
                std::memcmp(
                    vid, db_.get_latest_voted_block_id().bytes, 32) != 0) {
                kv_->rd_tag_mismatch.fetch_add(1, std::memory_order_relaxed);
            }
        }
        kv_->rd_tag_retries.store(
            kv_reader_tag_retries(kv_rd_), std::memory_order_relaxed);
    }
    // The block just committed is an undecided proposal: pin it BY ITS ID and
    // read through that pin, which is what an RPC request for `latest` does.
    // A perturbed id must not pin -- otherwise an id-blind pin returning some
    // sibling's root would pass the comparison whenever a height has one
    // proposal, which is most of the time.
    {
        mpt::Nibbles const prop = proposal_prefix(block_id);
        Node::SharedPtr const proot = db_.load_root_for_version(block);
        int64_t const ph = kv_reader_protect_block(kv_rd_, block, block_id.bytes);
        if (ph < 0) {
            kv_->rd_prop_checked.fetch_add(1, std::memory_order_relaxed);
            kv_->rd_prop_mismatch.fetch_add(1, std::memory_order_relaxed);
        }
        else {
            for (auto const &[a, slot] : sample) {
                kv_->rd_prop_checked.fetch_add(1, std::memory_order_relaxed);
                unsigned char bal[32], chash[32];
                uint64_t nonce = 0;
                bool const got =
                    kv_reader_account(kv_rd_, ph, a.bytes, bal, chash, &nonce);
                std::optional<Account> const td_a =
                    td_read_account_at(proot, block, a, prop);
                bool ok;
                if (got != td_a.has_value()) {
                    ok = false;
                }
                else if (got) {
                    unsigned char td_bal[32];
                    store_be(td_bal, td_a->balance);
                    ok = nonce == td_a->nonce &&
                         std::memcmp(bal, td_bal, 32) == 0 &&
                         std::memcmp(chash, td_a->code_hash.bytes, 32) == 0;
                }
                else {
                    ok = true;
                }
                if (!ok) {
                    kv_->rd_prop_mismatch.fetch_add(
                        1, std::memory_order_relaxed);
                }
                if (slot.has_value()) {
                    kv_->rd_prop_checked.fetch_add(
                        1, std::memory_order_relaxed);
                    unsigned char v[32];
                    kv_reader_storage(kv_rd_, ph, a.bytes, slot->bytes, v);
                    bytes32_t const td_v =
                        td_read_storage_at(proot, block, a, *slot, prop);
                    if (std::memcmp(v, td_v.bytes, 32) != 0) {
                        kv_->rd_prop_mismatch.fetch_add(
                            1, std::memory_order_relaxed);
                    }
                }
            }
            kv_reader_end_protect(kv_rd_, ph);
        }
        // One absent id on each side of the real one, so the check does not
        // depend on which way a perturbation happens to fall: a lower_bound
        // pin would accept the id above it (landing on the real proposal) even
        // though it rejects the one below.
        bytes32_t wrong[2];
        std::memset(wrong[0].bytes, 0x00, 32);
        std::memset(wrong[1].bytes, 0xff, 32);
        for (auto const &w : wrong) {
            kv_->rd_prop_checked.fetch_add(1, std::memory_order_relaxed);
            int64_t const bad = kv_reader_protect_block(kv_rd_, block, w.bytes);
            if (bad >= 0) { // pinned a proposal id that does not exist
                kv_->rd_prop_mismatch.fetch_add(1, std::memory_order_relaxed);
                kv_reader_end_protect(kv_rd_, bad);
            }
        }
    }
    // Read at the finalized tip, the same target an RPC state request pins. Skip
    // while it is outside triedb's history window (nothing to compare against).
    uint64_t const f = kv_reader_cursor(kv_rd_, /*finalized*/ 0);
    if (f == kv::KV_BLOCK_NONE || f == 0) {
        return;
    }
    uint64_t const hist = db_.get_history_length();
    uint64_t const td_earliest = f >= hist ? f - hist + 1 : 0;
    if (f < td_earliest) {
        return;
    }
    int64_t const h = kv_reader_protect_block(kv_rd_, f, nullptr);
    if (h < 0) {
        kv_->rd_pin_fail.fetch_add(1, std::memory_order_relaxed);
        return;
    }
    kv_->rd_pins.fetch_add(1, std::memory_order_relaxed);
    if (kv_rd_base_block_ == 0) {
        kv_rd_base_block_ = f; // the base image block (no blobs of its own)
    }
    Node::SharedPtr const troot = db_.load_root_for_version(f);
    for (auto const &[a, slot] : sample) {
        // account: reader (packed FFI form) vs triedb at version f
        kv_->rd_acc_checked.fetch_add(1, std::memory_order_relaxed);
        unsigned char bal[32], chash[32];
        uint64_t nonce = 0;
        bool const got =
            kv_reader_account(kv_rd_, h, a.bytes, bal, chash, &nonce);
        std::optional<Account> const td_a =
            td_read_account_at(troot, f, a, finalized_nibbles);
        bool acc_ok;
        if (got != td_a.has_value()) {
            acc_ok = false;
        }
        else if (got) {
            unsigned char td_bal[32];
            store_be(td_bal, td_a->balance);
            acc_ok = nonce == td_a->nonce &&
                     std::memcmp(bal, td_bal, 32) == 0 &&
                     std::memcmp(chash, td_a->code_hash.bytes, 32) == 0;
        }
        else {
            acc_ok = true;
        }
        if (!acc_ok) {
            kv_->rd_acc_mismatch.fetch_add(1, std::memory_order_relaxed);
        }
        // code: reader's global code-tree lookup vs triedb's code for the hash
        if (got && std::memcmp(chash, NULL_HASH.bytes, 32) != 0) {
            kv_->rd_code_checked.fetch_add(1, std::memory_order_relaxed);
            unsigned char const *cbuf = nullptr;
            uint64_t clen = 0;
            bytes32_t ch{};
            std::memcpy(ch.bytes, chash, 32);
            vm::SharedIntercode const td_c = read_code(ch);
            bool const rc = kv_reader_code(kv_rd_, chash, &cbuf, &clen);
            bool const code_ok =
                rc && td_c && clen == td_c->size() &&
                (clen == 0 || std::memcmp(cbuf, td_c->code(), clen) == 0);
            if (!code_ok) {
                kv_->rd_code_mismatch.fetch_add(1, std::memory_order_relaxed);
            }
            kv_reader_free(cbuf);
        }
        // storage: reader slot vs triedb slot
        if (slot.has_value()) {
            kv_->rd_sto_checked.fetch_add(1, std::memory_order_relaxed);
            unsigned char v[32];
            kv_reader_storage(kv_rd_, h, a.bytes, slot->bytes, v);
            bytes32_t const td_v =
                td_read_storage_at(troot, f, a, *slot, finalized_nibbles);
            if (std::memcmp(v, td_v.bytes, 32) != 0) {
                kv_->rd_sto_mismatch.fetch_add(1, std::memory_order_relaxed);
            }
        }
    }
    // Blob + index round trip. The header blob must be present, and
    // keccak(header) must resolve through the block-hash index back to f.
    if (f > kv_rd_base_block_) {
        kv_->rd_blob_checked.fetch_add(1, std::memory_order_relaxed);
        unsigned char const *hb = nullptr;
        uint64_t hlen = 0;
        bool const ok =
            kv_reader_block_blob(kv_rd_, h, kv::BLOB_HEADER, &hb, &hlen);
        if (!ok || hlen == 0) {
            kv_->rd_blob_mismatch.fetch_add(1, std::memory_order_relaxed);
        }
        else {
            kv_->rd_index_checked.fetch_add(1, std::memory_order_relaxed);
            bytes32_t const bh = to_bytes(keccak256({hb, hlen}));
            uint64_t num = 0;
            if (!kv_reader_resolve_block_hash(kv_rd_, bh.bytes, &num) ||
                num != f) {
                kv_->rd_index_mismatch.fetch_add(1, std::memory_order_relaxed);
            }
        }
        kv_reader_free(hb);
    }
    // The tx-hash blob's first hash must resolve to (f, 0) in the tx index.
    if (f > kv_rd_base_block_) {
        unsigned char const *tb = nullptr;
        uint64_t tlen = 0;
        if (kv_reader_block_blob(kv_rd_, h, kv::BLOB_TXHASHES, &tb, &tlen) &&
            tlen >= 32) {
            uint64_t const ntx = tlen / 32;
            // Per-tx table categories must cover exactly this many txs.
            uint32_t const tabs[] = {
                kv::BLOB_RECEIPTS, kv::BLOB_TXNS, kv::BLOB_CALLFRAMES};
            for (uint32_t const cat : tabs) {
                if (!kv_reader_blob_present(kv_rd_, h, cat)) {
                    continue; // category absent for this block
                }
                kv_->rd_tx_checked.fetch_add(1, std::memory_order_relaxed);
                if (kv_reader_table_count(kv_rd_, h, cat) !=
                    static_cast<int64_t>(ntx)) {
                    kv_->rd_tx_mismatch.fetch_add(
                        1, std::memory_order_relaxed);
                }
            }
            // Every tx: its hash resolves to (f, i), and each present per-tx
            // category has a non-empty blob at index i.
            for (uint64_t i = 0; i < ntx; ++i) {
                kv_->rd_index_checked.fetch_add(1, std::memory_order_relaxed);
                uint64_t blk = 0;
                uint32_t idx = ~uint32_t{0};
                if (!kv_reader_resolve_tx_hash(
                        kv_rd_, tb + i * 32, &blk, &idx) ||
                    blk != f || idx != static_cast<uint32_t>(i)) {
                    kv_->rd_index_mismatch.fetch_add(
                        1, std::memory_order_relaxed);
                }
                for (uint32_t const cat : tabs) {
                    if (!kv_reader_blob_present(kv_rd_, h, cat)) {
                        continue;
                    }
                    kv_->rd_tx_checked.fetch_add(1, std::memory_order_relaxed);
                    unsigned char const *eb = nullptr;
                    uint64_t elen = 0;
                    bool const ok = kv_reader_tx_blob(
                        kv_rd_, h, cat, static_cast<uint32_t>(i), &eb, &elen);
                    if (!ok || elen == 0) {
                        kv_->rd_tx_mismatch.fetch_add(
                            1, std::memory_order_relaxed);
                    }
                    kv_reader_free(eb);
                }
            }
        }
        kv_reader_free(tb);
    }
    kv_reader_end_protect(kv_rd_, h);
    // Failure path: a block below the retained window must not pin. Uses
    // oldest-1 (0 is never a real block here), so this only runs once pruning
    // has actually advanced the floor past the base image block.
    {
        uint64_t const o = kv_reader_cursor(kv_rd_, /*oldest*/ 1);
        if (o != kv::KV_BLOCK_NONE && o > kv_rd_base_block_) {
            kv_->rd_pruned_checked.fetch_add(1, std::memory_order_relaxed);
            int64_t const bad = kv_reader_protect_block(kv_rd_, o - 1, nullptr);
            if (bad >= 0) { // pinned a pruned block: wrong
                kv_->rd_pruned_mismatch.fetch_add(
                    1, std::memory_order_relaxed);
                kv_reader_end_protect(kv_rd_, bad);
            }
        }
    }
    kv_reader_hold_step(sample);
}

// KVDB_RDHOLD: pin the oldest retained block once and hold it across commits,
// re-reading the captured keys each block. Exec's prune advances past that block
// while the pin stands, so its block root must be deferred (see hz_deferred) and
// the pinned snapshot must stay both readable and unchanged.
void TrieDb::kv_reader_hold_step(
    std::vector<std::pair<Address, std::optional<bytes32_t>>> const &sample)
{
    if (kv_hold_n_ == 0) {
        return;
    }
    if (kv_hold_h_ < 0) { // not pinned yet: pin the oldest retained block
        if (!kv_hold_.empty()) {
            return; // already ran to completion
        }
        uint64_t const o = kv_reader_cursor(kv_rd_, /*oldest*/ 1);
        if (o == kv::KV_BLOCK_NONE || o == 0) {
            return;
        }
        int64_t const hh = kv_reader_protect_block(kv_rd_, o, nullptr);
        if (hh < 0) {
            kv_->rd_pin_fail.fetch_add(1, std::memory_order_relaxed);
            return;
        }
        kv_hold_h_ = hh;
        kv_hold_block_ = o;
        kv_hold_left_ = kv_hold_n_;
        // Capture the snapshot: what these keys read as at pin time.
        for (auto const &[a, slot] : sample) {
            KvHoldEntry e{};
            e.addr = a;
            e.has_slot = slot.has_value();
            if (e.has_slot) {
                e.slot = *slot;
            }
            uint64_t nonce = 0;
            e.got = kv_reader_account(
                kv_rd_, kv_hold_h_, a.bytes, e.acct, e.acct + 32, &nonce);
            std::memcpy(e.acct + 64, &nonce, 8);
            if (e.has_slot) {
                kv_reader_storage(
                    kv_rd_, kv_hold_h_, a.bytes, e.slot.bytes, e.val.bytes);
            }
            kv_hold_.push_back(e);
        }
        std::fprintf(
            stderr,
            "KVDB_RDHOLD: pinned block=%lu, holding %lu commits, %zu keys\n",
            kv_hold_block_,
            kv_hold_n_,
            kv_hold_.size());
        return;
    }
    // Held: re-read every captured key through the same handle; nothing may move.
    kv_->rd_hold_blocks.fetch_add(1, std::memory_order_relaxed);
    for (auto const &e : kv_hold_) {
        kv_->rd_hold_checked.fetch_add(1, std::memory_order_relaxed);
        unsigned char acct[72];
        uint64_t nonce = 0;
        bool const got = kv_reader_account(
            kv_rd_, kv_hold_h_, e.addr.bytes, acct, acct + 32, &nonce);
        std::memcpy(acct + 64, &nonce, 8);
        bool ok = (got == e.got) &&
                  (!got || std::memcmp(acct, e.acct, 72) == 0);
        if (ok && e.has_slot) {
            bytes32_t v{};
            kv_reader_storage(
                kv_rd_, kv_hold_h_, e.addr.bytes, e.slot.bytes, v.bytes);
            ok = std::memcmp(v.bytes, e.val.bytes, 32) == 0;
        }
        if (!ok) {
            kv_->rd_hold_mismatch.fetch_add(1, std::memory_order_relaxed);
        }
    }
    if (--kv_hold_left_ == 0) {
        kv_reader_end_protect(kv_rd_, kv_hold_h_);
        kv_hold_h_ = -1;
        std::fprintf(
            stderr,
            "KVDB_RDHOLD: released block=%lu after %lu commits\n",
            kv_hold_block_,
            kv_hold_n_);
    }
}

void TrieDb::kv_mv_validate(
    uint64_t const block, bytes32_t const &block_id,
    std::vector<std::pair<Address, std::optional<bytes32_t>>> const &sample)
{
    if (!kv_ || !kv_->shadow_ || sample.empty()) {
        return;
    }
    // Undecided-proposal check: this block was just committed as a proposal and
    // is not finalized yet, so triedb holds it under proposal_prefix(block_id) at
    // this version. Compare KV's tip (root_) to triedb's proposal subtrie. Runs
    // every block; in the keep-undecided tail this exercises proposals built on
    // unfinalized parents.
    {
        mpt::Nibbles const prop = proposal_prefix(block_id);
        Node::SharedPtr const proot = db_.load_root_for_version(block);
        for (auto const &[a, slot] : sample) {
            kv_->up_acc_checked.fetch_add(1, std::memory_order_relaxed);
            std::optional<Account> const kv_a = kv_read_account(a);
            std::optional<Account> const td_a =
                td_read_account_at(proot, block, a, prop);
            bool acc_ok;
            if (kv_a.has_value() != td_a.has_value()) {
                acc_ok = false;
            }
            else if (kv_a.has_value()) {
                acc_ok =
                    std::memcmp(&kv_a.value(), &td_a.value(), sizeof(Account)) ==
                    0;
            }
            else {
                acc_ok = true;
            }
            if (!acc_ok) {
                kv_->up_acc_mismatch.fetch_add(1, std::memory_order_relaxed);
            }
            if (slot.has_value()) {
                kv_->up_sto_checked.fetch_add(1, std::memory_order_relaxed);
                bytes32_t const kv_v = kv_read_storage(a, *slot);
                bytes32_t const td_v =
                    td_read_storage_at(proot, block, a, *slot, prop);
                if (std::memcmp(kv_v.bytes, td_v.bytes, 32) != 0) {
                    kv_->up_sto_mismatch.fetch_add(1, std::memory_order_relaxed);
                }
            }
        }
    }
    static constexpr uint64_t lags[] = {64, 256};
    uint64_t const hist = db_.get_history_length();
    uint64_t const td_earliest = block >= hist ? block - hist + 1 : 0;
    for (uint64_t const lag : lags) {
        if (block < lag) {
            continue;
        }
        uint64_t const k = block - lag;
        if (!kv_->mv_has(k) || k < td_earliest) {
            kv_->mv_skipped.fetch_add(1, std::memory_order_relaxed);
            continue;
        }
        uint64_t const kroot = kv_->finalized_state_root(k);
        Node::SharedPtr const troot = db_.load_root_for_version(k);
        for (auto const &[a, slot] : sample) {
            kv_->mv_acc_checked.fetch_add(1, std::memory_order_relaxed);
            std::optional<Account> const kv_a = kv_read_account_at(a, kroot);
            std::optional<Account> const td_a =
                td_read_account_at(troot, k, a, finalized_nibbles);
            bool acc_ok;
            if (kv_a.has_value() != td_a.has_value()) {
                acc_ok = false;
            }
            else if (kv_a.has_value()) {
                acc_ok =
                    std::memcmp(&kv_a.value(), &td_a.value(), sizeof(Account)) ==
                    0;
            }
            else {
                acc_ok = true;
            }
            if (!acc_ok) {
                kv_->mv_acc_mismatch.fetch_add(1, std::memory_order_relaxed);
            }
            if (slot.has_value()) {
                kv_->mv_sto_checked.fetch_add(1, std::memory_order_relaxed);
                bytes32_t const kv_v = kv_read_storage_at(a, *slot, kroot);
                bytes32_t const td_v =
                    td_read_storage_at(troot, k, a, *slot, finalized_nibbles);
                if (std::memcmp(kv_v.bytes, td_v.bytes, 32) != 0) {
                    kv_->mv_sto_mismatch.fetch_add(
                        1, std::memory_order_relaxed);
                }
            }
        }
    }
}
#endif

storage_page_t TrieDb::read_storage_page(
    Address const &addr, Incarnation const incarnation,
    bytes32_t const &page_key)
{
    if (!page_encoded_) {
        MONAD_ABORT("read_storage_page is only valid on a page-encoded TrieDb");
    }
    else {
        storage_page_t result;
        if (cache_ && cache_->try_read_storage_page(
                          addr, incarnation, page_key, result)) {
            return result;
        }
        auto const res = db_.find(
            curr_root_,
            concat(
                prefix_,
                STATE_NIBBLE,
                NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
                NibblesView{
                    keccak256({page_key.bytes, sizeof(page_key.bytes)})}),
            block_number_);
        if (res.has_error()) {
            stats_storage_no_value();
            return {};
        }
        stats_storage_value();
        auto encoded_storage = res.value().node->value();
        auto const value = decode_storage_db_ignore_key(encoded_storage);
        MONAD_ASSERT(!value.has_error());
        auto const page = decode_storage_page(value.value());
        MONAD_ASSERT(!page.has_error());
        return page.value();
    }
}

#if KVDB_PROTO
vm::SharedIntercode TrieDb::kv_read_code(bytes32_t const &code_hash)
{
    ::boost::fibers::promise<std::optional<byte_string>> promise;
    auto fut = promise.get_future();
    db_.post_to_io_thread(
        [this, code_hash, p = std::move(promise)](
            MONAD_ASYNC_NAMESPACE::AsyncIO &) mutable {
            p.set_value(kv_->lookup_code(code_hash));
        });
    auto const r = fut.get();
    return r ? vm::make_shared_intercode(byte_string_view{r->data(), r->size()})
             : vm::make_shared_intercode({});
}

void TrieDb::kv_shadow_code(
    bytes32_t const &code_hash, vm::SharedIntercode const &td)
{
    if (!kv_) {
        return;
    }
    kv_->code_checked.fetch_add(1, std::memory_order_relaxed);
    auto const kv = kv_read_code(code_hash);
    bool const ok = kv->size() == td->size() &&
                    (td->size() == 0 ||
                     std::memcmp(kv->code(), td->code(), td->size()) == 0);
    if (!ok) {
        kv_->code_mismatch.fetch_add(1, std::memory_order_relaxed);
    }
}
#endif

vm::SharedIntercode TrieDb::read_code(bytes32_t const &code_hash)
{
#if KVDB_PROTO
    if (kv_serves()) {
        return kv_read_code(code_hash); // KV serves the read (perf mode)
    }
    // Tag this find as a code read so its node reads go to the trie_code metric
    // bucket, not trie_acct/trie_stor (kept comparable to kv, which serves no
    // code).
    ::monad::kvdb_metrics::find_kind = ::monad::kvdb_metrics::LookupKind::code;
#endif
    auto const res = db_.find(
        curr_root_,
        concat(
            prefix_,
            CODE_NIBBLE,
            NibblesView{to_byte_string_view(code_hash.bytes)}),
        block_number_);
    auto const td = res.has_error()
                        ? vm::make_shared_intercode({})
                        : vm::make_shared_intercode(res.value().node->value());
#if KVDB_PROTO
    kv_shadow_code(code_hash, td);
#endif
    return td;
}

void TrieDb::commit(
    bytes32_t const &block_id, CommitBuilder &builder,
    BlockHeader const &header,
    [[maybe_unused]] StateDeltas const &state_deltas,
    [[maybe_unused]] Code const &code,
    std::function<void(BlockHeader &)> const populate_header_fn)
{
    // The builder must be a PageCommitBuilder iff this db is page-encoded;
    // PageCommitBuilder is the only builder that produces page-keyed updates.
    MONAD_ASSERT_PRINTF(
        (dynamic_cast<PageCommitBuilder const *>(&builder) != nullptr) ==
            is_page_encoded(),
        "encoding mismatch at block %lu: TrieDb::is_page_encoded=%d but commit "
        "builder is of wrong type",
        header.number,
        is_page_encoded());

    auto const block_number = header.number;
    MONAD_ASSERT(block_number <= std::numeric_limits<int64_t>::max());

    MONAD_ASSERT(block_id != bytes32_t{});
    if (db_.is_on_disk() && block_id != proposal_block_id_) {
        auto const dest_prefix = proposal_prefix(block_id);
        if (db_.get_latest_version() != INVALID_BLOCK_NUM) {
            MONAD_ASSERT(block_number != block_number_);
            curr_root_ = db_.copy_trie(
                curr_root_,
                prefix_,
                db_.load_root_for_version(block_number),
                dest_prefix,
                block_number,
                false);
        }
        proposal_block_id_ = block_id;
        prefix_ = dest_prefix;
    }
    block_number_ = block_number;

    curr_root_ = db_.upsert(
        std::move(curr_root_),
        builder.build(prefix_),
        block_number_,
        true,
        true,
        false);

    BlockHeader complete_header = header;
    MONAD_ASSERT(populate_header_fn);
    populate_header_fn(complete_header);

    builder.add_block_header(complete_header);
    curr_root_ = db_.upsert(
        std::move(curr_root_), builder.build(prefix_), block_number_, false);

    if (cache_) {
        cache_->update_proposal_state(
            builder.take_proposal_post_state(), header.number, block_id);
    }

#if KVDB_PROTO
    // item 1: extract this block's KV updates and log a summary. No tree
    // writes yet (item 2). Gated on kv_ so it only runs in proto runs.
    if (kv_) {
        auto const ups = kv::extract_updates(state_deltas);
        bytes32_t const zero{};
        size_t n_set = 0, n_del = 0, n_slot_set = 0, n_slot_rm = 0;
        for (auto const &au : ups) {
            if (au.op == kv::AcctOp::Set) {
                ++n_set;
            }
            else {
                ++n_del;
            }
            for (auto const &s : au.slots) {
                if (std::memcmp(s.value.bytes, zero.bytes, 32) == 0) {
                    ++n_slot_rm;
                }
                else {
                    ++n_slot_set;
                }
            }
        }
        // items 2+3: apply the updates to KV and advance its root, so the
        // next block's reads see this block's state. Runs on the io service
        // thread (device reads via the shared pool); the exec fiber blocks
        // until it completes. `ups` outlives the task (fiber suspended here).
        // RLP of the complete header: keccak -> block hash H (stored in the leaf
        // for index prune / number->hash), and the same bytes are this block's
        // header blob (no re-encode). Same H the driver computes post-commit.
        byte_string const hdr_rlp = rlp::encode_block_header(complete_header);
        bytes32_t const block_hash = to_bytes(keccak256(hdr_rlp));
        {
            auto const kv_cmt_begin = std::chrono::steady_clock::now();
            ::boost::fibers::promise<void> pr;
            auto fut = pr.get_future();
            db_.post_to_io_thread(
                [this, &ups, blk = block_number_, bid = block_id,
                 bh = block_hash, &hdr_rlp, &builder, p = std::move(pr)](
                    MONAD_ASYNC_NAMESPACE::AsyncIO &io) mutable {
                    kv_->commit_block(io, ups, blk, bid, bh, hdr_rlp, builder);
                    p.set_value();
                });
            fut.get();
            // kv_cmt phase: KV reads to construct new nodes + the node writes
            // (the exec fiber is blocked here, so this is that phase's latency).
            kv_->kv_commit_us_ = static_cast<uint64_t>(
                std::chrono::duration_cast<std::chrono::microseconds>(
                    std::chrono::steady_clock::now() - kv_cmt_begin)
                    .count());
        }
        // Write this block's new code (from block state, dedup by hash) into
        // KV's code B+tree, on the same io thread as the node commit.
        {
            ::boost::fibers::promise<void> pr;
            auto fut = pr.get_future();
            db_.post_to_io_thread(
                [this, &code, p = std::move(pr)](
                    MONAD_ASYNC_NAMESPACE::AsyncIO &) mutable {
                    kv_->write_code(code);
                    p.set_value();
                });
            fut.get();
        }
        // Multiversion historical-read validation (shadow mode only): sample a
        // few of this block's touched keys and compare KV-at-(T-D) to triedb at
        // version T-D. Public-typed sample so kv_mv_validate stays header-safe.
        {
            std::vector<std::pair<Address, std::optional<bytes32_t>>> sample;
            size_t const ns = std::min<size_t>(ups.size(), 4);
            sample.reserve(ns);
            for (size_t i = 0; i < ns; ++i) {
                std::optional<bytes32_t> slot;
                if (!ups[i].slots.empty()) {
                    slot = ups[i].slots[0].slot;
                }
                sample.emplace_back(ups[i].addr, slot);
            }
            kv_mv_validate(block_number_, block_id, sample);
            // RPC read-side validation on the same sample (KVDB_RDTEST=1):
            // drive a KvReader over the live store as the RPC process will.
            if (kv_rd_check_) {
                kv_reader_validate(block_number_, block_id, sample);
            }
        }
        std::fprintf(
            stderr,
            "KVDB_PROTO commit block=%lu: touched_accts=%zu accts[set=%zu "
            "del=%zu] slots[set=%zu rm=%zu] device_nodes=%lu\n",
            header.number,
            ups.size(),
            n_set,
            n_del,
            n_slot_set,
            n_slot_rm,
            kv_->image_bytes
                ? (kv_->write_pos_ - kv_->image_bytes) / kv::NODE_SIZE
                : 0);
    }
#endif
}

void TrieDb::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &block_id)
{
    if (cache_) {
        cache_->set_block_and_prefix(block_number, block_id);
    }
    // set read state
    if (!db_.is_on_disk()) {
        MONAD_ASSERT(proposal_block_id_ == bytes32_t{});
        block_number_ = block_number;
        return;
    }
    prefix_ =
        block_id == bytes32_t{} ? finalized_nibbles : proposal_prefix(block_id);
    if (block_number_ != block_number) {
        curr_root_ = db_.load_root_for_version(block_number);
        block_number_ = block_number;
    }
    MONAD_ASSERT_PRINTF(
        db_.find(curr_root_, prefix_, block_number).has_value(),
        "Fail to find block_number %lu, block_id %s",
        block_number,
        fmt::format("{}", block_id).c_str());
    proposal_block_id_ = block_id;
#if KVDB_PROTO
    // Position KV's proposal cursor on the same parent, so the next commit
    // builds its child from the correct (possibly unfinalized) parent root.
    if (kv_) {
        ::boost::fibers::promise<void> pr;
        auto fut = pr.get_future();
        db_.post_to_io_thread(
            [this, block_number, block_id, p = std::move(pr)](
                MONAD_ASYNC_NAMESPACE::AsyncIO &) mutable {
                kv_->set_tip(block_number, block_id);
                p.set_value();
            });
        fut.get();
    }
#endif
}

// also changes internal state to the finalized state
void TrieDb::finalize(uint64_t const block_number, bytes32_t const &block_id)
{
    auto const latest_finalized = db_.get_latest_finalized_version();
    MONAD_ASSERT_PRINTF(
        latest_finalized == INVALID_BLOCK_NUM ||
            block_number == latest_finalized ||
            block_number == latest_finalized + 1,
        "Finalized version must advance by at most one block. block to "
        "finalize %lu must equal latest_finalized %lu or latest_finalized + 1",
        block_number,
        latest_finalized);

    MONAD_ASSERT(block_id != bytes32_t{});
    if (db_.is_on_disk()) {
        auto const src_prefix = proposal_prefix(block_id);
        auto root = (block_number_ == block_number)
                        ? curr_root_
                        : db_.load_root_for_version(block_number);
        MONAD_ASSERT(db_.find(root, src_prefix, block_number).has_value());
        curr_root_ = db_.copy_trie(
            root, src_prefix, root, finalized_nibbles, block_number, true);
        prefix_ = finalized_nibbles;
    }
    block_number_ = block_number;
    db_.update_finalized_version(block_number);
    if (cache_) {
        cache_->on_finalize(block_number, block_id);
    }
#if KVDB_PROTO
    // Promote the finalized proposal's root into KV's finalized ring.
    if (kv_) {
        ::boost::fibers::promise<void> pr;
        auto fut = pr.get_future();
        db_.post_to_io_thread(
            [this, block_number, block_id, p = std::move(pr)](
                MONAD_ASYNC_NAMESPACE::AsyncIO &) mutable {
                kv_->finalize_block(block_number, block_id);
                p.set_value();
            });
        fut.get();
    }
#endif
}

void TrieDb::update_verified_block(uint64_t const block_number)
{
    auto const latest_verified = db_.get_latest_verified_version();
    MONAD_ASSERT_PRINTF(
        latest_verified == INVALID_BLOCK_NUM || block_number >= latest_verified,
        "block_number %lu must be gte last_verified %lu",
        block_number,
        latest_verified);
    db_.update_verified_version(block_number);
}

void TrieDb::update_voted_metadata(
    uint64_t const block_number, bytes32_t const &block_id)
{
    db_.update_voted_metadata(block_number, block_id);
#if KVDB_PROTO
    // Mirror into KV's shared metadata so RPC can resolve the `safe` tag.
    if (kv_) {
        ::boost::fibers::promise<void> pr;
        auto fut = pr.get_future();
        db_.post_to_io_thread(
            [this, block_number, block_id, p = std::move(pr)](
                MONAD_ASYNC_NAMESPACE::AsyncIO &) mutable {
                kv_->publish_voted(block_number, block_id);
                p.set_value();
            });
        fut.get();
    }
#endif
}

void TrieDb::update_proposed_metadata(
    uint64_t const block_number, bytes32_t const &block_id)
{
    db_.update_proposed_metadata(block_number, block_id);
#if KVDB_PROTO
    // Mirror into KV's shared metadata so RPC can resolve the `latest` tag.
    if (kv_) {
        ::boost::fibers::promise<void> pr;
        auto fut = pr.get_future();
        db_.post_to_io_thread(
            [this, block_number, block_id, p = std::move(pr)](
                MONAD_ASYNC_NAMESPACE::AsyncIO &) mutable {
                kv_->publish_proposed(block_number, block_id);
                p.set_value();
            });
        fut.get();
    }
#endif
}

bytes32_t TrieDb::state_root()
{
    return merkle_root(state_nibbles);
}

bytes32_t TrieDb::receipts_root()
{
    return merkle_root(receipt_nibbles);
}

bytes32_t TrieDb::transactions_root()
{
    return merkle_root(transaction_nibbles);
}

std::optional<bytes32_t> TrieDb::withdrawals_root()
{
    auto const res =
        db_.find(curr_root_, concat(prefix_, WITHDRAWAL_NIBBLE), block_number_);
    if (res.has_error()) {
        return std::nullopt;
    }
    auto const data = res.value().node->data();
    if (data.empty()) {
        return NULL_ROOT;
    }
    MONAD_ASSERT(data.size() == sizeof(bytes32_t));
    return to_bytes(data);
}

bytes32_t TrieDb::merkle_root(Nibbles const &nibbles)
{
    auto const res = db_.find(
        curr_root_, concat(prefix_, NibblesView{nibbles}), block_number_);
    if (!res.has_value() || res.value().node->data().empty()) {
        return NULL_ROOT;
    }
    auto const data = res.value().node->data();
    MONAD_ASSERT(data.size() == sizeof(bytes32_t));
    return to_bytes(data);
}

BlockHeader TrieDb::read_eth_header()
{
    auto const query_res = db_.find(
        curr_root_, concat(prefix_, BLOCKHEADER_NIBBLE), block_number_);
    MONAD_ASSERT(!query_res.has_error());
    auto encoded_header_db = query_res.value().node->value();
    auto decode_res = rlp::decode_block_header(encoded_header_db);
    MONAD_ASSERT_PRINTF(
        decode_res.has_value(),
        "FATAL: Could not decode eth header : %s",
        decode_res.error().message().c_str());
    return std::move(decode_res.value());
}

std::string TrieDb::print_stats()
{
    std::string ret;
    ret += std::format(
        ",ae={:4},ane={:4},sz={:4},snz={:4}",
        n_account_no_value_.load(std::memory_order_acquire),
        n_account_value_.load(std::memory_order_acquire),
        n_storage_no_value_.load(std::memory_order_acquire),
        n_storage_value_.load(std::memory_order_acquire));
    n_account_no_value_.store(0, std::memory_order_release);
    n_account_value_.store(0, std::memory_order_release);
    n_storage_no_value_.store(0, std::memory_order_release);
    n_storage_value_.store(0, std::memory_order_release);
    if (cache_) {
        ret += ",ac=" + cache_->accounts_stats() +
               ",sc=" + cache_->storage_stats();
    }
#if KVDB_PROTO
    // kv_cmt phase latency (KV commit: construct-reads + node writes). Note
    // the runloop's `cmt` still includes this; triedb-commit ~= cmt - kv_cmt.
    if (kv_) {
        ret += std::format(",kv_cmt={:>8}", kv_->kv_commit_us_);
    }
#endif
    return ret;
}

nlohmann::json TrieDb::to_json(size_t const concurrency_limit)
{
    struct Traverse : public TraverseMachine
    {
        TrieDb &db;
        nlohmann::json &json;
        Nibbles path{};

        explicit Traverse(TrieDb &db, nlohmann::json &json)
            : db(db)
            , json(json)
        {
        }

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(node.path_nibble_view().nibble_size() == 0);
                return true;
            }
            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            if (path.nibble_size() == (KECCAK256_SIZE * 2)) {
                handle_account(node);
            }
            else if (
                path.nibble_size() == ((KECCAK256_SIZE + KECCAK256_SIZE) * 2)) {
                handle_storage(node);
            }
            return true;
        }

        virtual void up(unsigned char const branch, Node const &node) override
        {
            auto const path_view = NibblesView{path};
            auto const rem_size = [&] {
                if (branch == INVALID_BRANCH) {
                    MONAD_ASSERT(path_view.nibble_size() == 0);
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                MONAD_ASSERT(rem_size >= 0);
                MONAD_ASSERT(
                    path_view.substr(static_cast<unsigned>(rem_size)) ==
                    concat(branch, node.path_nibble_view()));
                return rem_size;
            }();
            path = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        void handle_account(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            auto encoded_account = node.value();

            auto acct = decode_account_db(encoded_account);

            auto const key = fmt::format("{}", NibblesView{path});

            json[key]["address"] = fmt::format("{}", acct.value().first);
            json[key]["balance"] =
                fmt::format("{}", acct.value().second.balance);
            json[key]["nonce"] =
                fmt::format("0x{:x}", acct.value().second.nonce);

            auto const icode = db.read_code(acct.value().second.code_hash);
            MONAD_ASSERT(icode);
            json[key]["code"] = "0x" + to_hex({icode->code(), icode->size()});

            if (!json[key].contains("storage")) {
                json[key]["storage"] = nlohmann::json::object();
            }
        }

        void handle_storage(Node const &node)
        {
            MONAD_ASSERT(node.has_value());

            auto encoded_storage = node.value();
            auto raw_res = decode_storage_db_raw(encoded_storage);
            MONAD_ASSERT(raw_res.has_value());

            auto const acct_key = fmt::format(
                "{}", NibblesView{path}.substr(0, KECCAK256_SIZE * 2));

            if (db.is_page_encoded()) {
                // Page-encoded leaf: first element of the RLP list is the
                // page_key (compact), second is the encoded page bytes.
                // Fan out one JSON entry per populated slot, keyed by
                // keccak256(slot_key) so the output matches a slot dump.
                bytes32_t const page_key = to_bytes(raw_res.value().first);
                auto const page = decode_storage_page(raw_res.value().second);
                MONAD_ASSERT(page.has_value());
                for (uint8_t off = 0; off < storage_page_t::SLOTS; ++off) {
                    auto const &slot_value = page.value()[off];
                    if (slot_value == bytes32_t{}) {
                        continue;
                    }
                    bytes32_t const slot_key = compute_slot_key(page_key, off);
                    auto const hashed_slot_key = to_bytes(
                        keccak256({slot_key.bytes, sizeof(slot_key.bytes)}));
                    auto const key = fmt::format("{}", hashed_slot_key);
                    auto storage_data_json = nlohmann::json::object();
                    storage_data_json["slot"] = fmt::format(
                        "0x{:02x}",
                        fmt::join(
                            std::as_bytes(std::span(slot_key.bytes)), ""));
                    storage_data_json["value"] = fmt::format(
                        "0x{:02x}",
                        fmt::join(
                            std::as_bytes(std::span(slot_value.bytes)), ""));
                    json[acct_key]["storage"][key] = storage_data_json;
                }
            }
            else {
                // Slot-encoded leaf: trie path under the account is
                // keccak256(slot_key); the leaf carries (slot_key,
                // slot_value).
                bytes32_t const slot_key = to_bytes(raw_res.value().first);
                bytes32_t const slot_value = to_bytes(raw_res.value().second);
                auto const key = fmt::format(
                    "{}",
                    NibblesView{path}.substr(
                        KECCAK256_SIZE * 2, KECCAK256_SIZE * 2));

                auto storage_data_json = nlohmann::json::object();
                storage_data_json["slot"] = fmt::format(
                    "0x{:02x}",
                    fmt::join(std::as_bytes(std::span(slot_key.bytes)), ""));
                storage_data_json["value"] = fmt::format(
                    "0x{:02x}",
                    fmt::join(std::as_bytes(std::span(slot_value.bytes)), ""));
                json[acct_key]["storage"][key] = storage_data_json;
            }
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }
    };

    auto json = nlohmann::json::object();
    Traverse traverse(*this, json);

    auto res_cursor =
        db_.find(curr_root_, concat(prefix_, STATE_NIBBLE), block_number_);
    MONAD_ASSERT(res_cursor.has_value());
    MONAD_ASSERT(res_cursor.value().is_valid());
    // RWOndisk Db prevents any parallel traversal that does blocking i/o
    // from running on the triedb thread, which include to_json. Thus, we can
    // only use blocking traversal for RWOnDisk Db, but can still do parallel
    // traverse in other cases.
    if (db_.is_on_disk() && !db_.is_read_only()) {
        MONAD_ASSERT(
            db_.traverse_blocking(res_cursor.value(), traverse, block_number_));
    }
    else {
        MONAD_ASSERT(db_.traverse(
            res_cursor.value(), traverse, block_number_, concurrency_limit));
    }

    return json;
}

uint64_t TrieDb::get_block_number() const
{
    return block_number_;
}

uint64_t TrieDb::get_history_length() const
{
    return db_.get_history_length();
}

#if KVDB_PROTO
// ── KV-DB prototype: RPC read-side opener with hazard-pointer block protection ─
// A standalone read-only view over the flat-page KV device, driven by the RPC
// process (rust/crates/monad-triedb ffi). Reuses the file-local kv:: node format,
// block-map descent, and the shared-memory hazard array (kv::HazardArray) that
// exec scans for reclamation. No writer state: block-map pages are read by plain
// pread(base_ + ref); the meta region is mmap'd read-only to observe the live
// block-map root exec publishes. All operations are synchronous.
struct KvReader
{
    // Block-map contract, MUST match TrieDb::BM_* (block-map key/value layout):
    // key = (block big-endian 8B, id 32B); value = (block_root 8B, parent_id 32B,
    // block_hash 32B). block_root (value[0:8]) is the single HP2-protected,
    // separately-retired per-block root.
    static constexpr size_t BM_KL = 40, BM_VL = 72;

    int dev_fd_ = -1;
    uint64_t base_ = 0; // .kvhdr base_offset: device byte offset of node ref 0
    void *meta_map_ = nullptr;
    kv::KvMeta const *meta_ = nullptr;
    kv::HazardArray haz_;

    // Read-only page store for block-map descent. One buffer, valid until the
    // next read() — matches kv::blockmap's contract (a node's fields are fully
    // consumed before any nested read()).
    struct RStore
    {
        KvReader *r;
        std::array<unsigned char, kv::NODE_SIZE> buf;
        unsigned char const *read(uint64_t const ref)
        {
            ssize_t const n = ::pread(
                r->dev_fd_, buf.data(), kv::NODE_SIZE,
                static_cast<off_t>(r->base_ + ref));
            MONAD_ASSERT(n == static_cast<ssize_t>(kv::NODE_SIZE));
            return buf.data();
        }
    };

    // seq_cst load of the live block-map root exec publishes into the shared meta
    // mapping (pairs with install_block_map_root's seq_cst store + the HP fences).
    uint64_t live_tree_root() const
    {
        return __atomic_load_n(&meta_->tree_root, __ATOMIC_SEQ_CST);
    }

    // Attach the store read-only. `kvhdr_path` is the .kvhdr sidecar (base_offset);
    // the device comes from $KVDB_DEVICE (default /dev/triedb). Exec must already
    // be up (the hazard segment and meta must exist). Returns false on any error.
    bool open(char const *const kvhdr_path)
    {
        int const sfd = ::open(kvhdr_path, O_RDONLY);
        if (sfd == -1) {
            return false;
        }
        kv::KvHeader hdr{};
        ssize_t const hr = ::read(sfd, &hdr, sizeof(hdr));
        ::close(sfd);
        if (hr != static_cast<ssize_t>(sizeof(hdr)) || hdr.magic != kv::MAGIC ||
            hdr.node_size != kv::NODE_SIZE) {
            return false;
        }
        base_ = hdr.base_offset;
        char const *const dev = std::getenv("KVDB_DEVICE");
        dev_fd_ = ::open(dev != nullptr ? dev : "/dev/triedb", O_RDONLY);
        if (dev_fd_ == -1) {
            return false;
        }
        void *const m = ::mmap(
            nullptr, KVDB_META_BYTES, PROT_READ, MAP_SHARED, dev_fd_,
            static_cast<off_t>(base_));
        if (m == MAP_FAILED) {
            return false;
        }
        meta_map_ = m;
        meta_ = static_cast<kv::KvMeta const *>(m);
        if (meta_->magic != kv::META_MAGIC || meta_->version != 7 ||
            meta_->node_size != kv::NODE_SIZE) {
            return false;
        }
        return haz_.open("/kvdb_hazards"); // attach exec's segment (no create)
    }

    void close()
    {
        haz_.close();
        if (meta_map_ != nullptr) {
            ::munmap(meta_map_, KVDB_META_BYTES);
            meta_map_ = nullptr;
        }
        if (dev_fd_ != -1) {
            ::close(dev_fd_);
            dev_fd_ = -1;
        }
    }

    // Pin `block` for the duration of a request. Two-hazard protocol:
    //   HP1 (transient) pins the live block-map root while we walk it;
    //   HP2 (request-long) pins the found block root; HP1 is then dropped.
    // Returns the hazard slot as an opaque handle (>= 0), or -1 if `block` is not
    // a retained block (pruned / never existed). The handle's HP2 holds the block
    // root; state/blob reads descend from it (subsequent FFI, not yet built).
    // Pin one block-map entry. `id` names a specific proposal; passing nullptr
    // takes the finalized entry at that height, which finalize_block has made
    // unique by unlinking the siblings -- so the id-0 lower_bound probe is
    // unambiguous only there, which is why an undecided block must give its id.
    int64_t protect_block(uint64_t const block, unsigned char const *const id)
    {
        unsigned char probe[BM_KL], k[BM_KL], v[BM_VL];
        for (int b = 0; b < 8; ++b) {
            probe[b] = static_cast<unsigned char>(block >> (56 - 8 * b));
        }
        if (id != nullptr) {
            std::memcpy(probe + 8, id, 32);
        }
        else {
            std::memset(probe + 8, 0, 32);
        }

        uint32_t const slot = haz_.acquire();
        for (;;) {
            // HP1: pin the live block-map root, then confirm it is still current.
            // Once confirmed, exec cannot free it (it would be retired while our
            // hazard names it), so the walk below is safe.
            uint64_t const root = live_tree_root();
            haz_.publish1(slot, root);
            if (live_tree_root() != root) {
                continue; // root advanced before our pin took effect; re-pin
            }
            RStore st{this};
            if (id != nullptr) {
                // An exact (block, id) hit is the proposal itself: no sibling
                // can be mistaken for it, so no block check is needed.
                if (!kv::blockmap::lookup(
                        st, root, probe, BM_KL, BM_VL, v)) {
                    haz_.release(slot);
                    return -1; // no such proposal
                }
            }
            else {
                if (!kv::blockmap::lower_bound(
                        st, root, probe, BM_KL, BM_VL, k, v)) {
                    haz_.release(slot);
                    return -1; // no entry >= block
                }
                uint64_t kblock = 0;
                for (int b = 0; b < 8; ++b) {
                    kblock = (kblock << 8) | k[b];
                }
                if (kblock != block) {
                    haz_.release(slot);
                    return -1; // block not present
                }
            }
            uint64_t block_root;
            std::memcpy(&block_root, v, 8);
            // HP2: pin the block root, then re-validate the block map. If the root
            // is unchanged, the mapping we read is still live, so the entry has
            // not gone away since our read (pruned, or unlinked as a finalize
            // loser) -> block_root has not been retired -> HP2 was published
            // while it was still live -> protected.
            haz_.publish2(slot, block_root);
            if (live_tree_root() != root) {
                haz_.publish2(slot, 0);
                continue; // map changed under us; re-resolve from scratch
            }
            haz_.publish1(slot, 0); // drop transient HP1; HP2 holds block_root
            return static_cast<int64_t>(slot);
        }
    }

    void end_protect(int64_t const handle)
    {
        if (handle >= 0) {
            haz_.release(static_cast<uint32_t>(handle));
        }
    }

    // The block root a handle protects (its HP2). A read carries the handle, so
    // no re-resolution and no side map.
    uint64_t handle_root(int64_t const handle) const
    {
        return haz_.peek2(static_cast<uint32_t>(handle));
    }

    // ── page + descent primitives ───────────────────────────────────────────
    void read_page(uint64_t const ref, unsigned char *const dst) const
    {
        ssize_t const n = ::pread(
            dev_fd_, dst, kv::NODE_SIZE, static_cast<off_t>(base_ + ref));
        MONAD_ASSERT(n == static_cast<ssize_t>(kv::NODE_SIZE));
    }

    // Descend from `root` to the leaf whose range contains `key`, copying that
    // leaf page into `out`. Mirrors kv::kv_to_leaf: N_BLOCK_ROOT descends like
    // N_INTERNAL (entries at HDR), and pick_child reads the node's own key
    // length, so one routine serves the account tree (20B keys) and a storage
    // subtree (32B). False if the root / a child is absent.
    bool to_leaf(
        uint64_t ref, unsigned char const *const key,
        unsigned char *const out) const
    {
        for (;;) {
            if (ref == kv::NULL_REF) {
                return false;
            }
            read_page(ref, out);
            if (out[0] != kv::N_INTERNAL && out[0] != kv::N_BLOCK_ROOT) {
                return true;
            }
            ref = kv::pick_child(out, key);
        }
    }

    // ── state reads (under a handle's pinned block root) ────────────────────
    // Account by address. Also yields the storage-root ref (NULL_REF when the
    // account has no storage subtree) so a slot read reuses this one descent.
    bool find_account(
        uint64_t const block_root, unsigned char const *const addr,
        Account &out, uint64_t &out_sref) const
    {
        unsigned char leaf[kv::NODE_SIZE];
        if (!to_leaf(block_root, addr, leaf) ||
            leaf[0] != kv::N_LEAF_ACCOUNT) {
            return false;
        }
        uint16_t count;
        std::memcpy(&count, leaf + 2, sizeof(count));
        unsigned char const *const p = leaf + kv::HDR;
        for (size_t i = 0; i < count; ++i) {
            unsigned char const *const rec = p + i * kv::ACCT_REC;
            if (std::memcmp(rec, addr, kv::ACCT_KEY) == 0) {
                std::memcpy(&out, rec + kv::ACCT_KEY, sizeof(Account));
                std::memcpy(
                    &out_sref, rec + kv::ACCT_KEY + sizeof(Account), 8);
                return true;
            }
        }
        return false;
    }

    // Slot value; zero when the account, the storage subtree, the page or the
    // slot is absent (KV stores no zero slots). Mirrors KvShadow::kv_deliver_slot
    // for both storage-leaf shapes (flat records, and page records addressed by
    // an offset table with a presence bitmap + optional out-of-line value page).
    bytes32_t read_slot(
        uint64_t const block_root, unsigned char const *const addr,
        bytes32_t const &key) const
    {
        Account a;
        uint64_t sref = kv::NULL_REF;
        if (!find_account(block_root, addr, a, sref) ||
            sref == kv::NULL_REF) {
            return bytes32_t{};
        }
        unsigned char leaf[kv::NODE_SIZE];
        if (!to_leaf(sref, key.bytes, leaf)) {
            return bytes32_t{};
        }
        uint16_t count;
        std::memcpy(&count, leaf + 2, sizeof(count));
        unsigned char const *const p = leaf + kv::HDR;
        if (leaf[0] == kv::N_LEAF_STORAGE_FLAT) {
            for (size_t i = 0; i < count; ++i) {
                unsigned char const *const rec = p + i * kv::STOR_REC_FLAT;
                if (std::memcmp(rec, key.bytes, kv::STOR_KEY) == 0) {
                    bytes32_t out{};
                    std::memcpy(out.bytes, rec + 32, 32);
                    return out;
                }
            }
            return bytes32_t{};
        }
        MONAD_ASSERT(leaf[0] == kv::N_LEAF_STORAGE_PAGE);
        bytes32_t base_key = key;
        base_key.bytes[31] =
            static_cast<unsigned char>(base_key.bytes[31] & 0x80);
        size_t const idx = static_cast<size_t>(key.bytes[31] & 0x7f);
        for (size_t i = 0; i < count; ++i) {
            uint16_t off;
            std::memcpy(&off, p + i * 2, sizeof(off));
            unsigned char const *const rec = leaf + off;
            if (std::memcmp(rec, base_key.bytes, kv::STOR_KEY) != 0) {
                continue;
            }
            unsigned char const *const bm = rec + kv::PG_BITMAP;
            if (!kv::bit_test(bm, idx)) {
                return bytes32_t{}; // slot not present in the page
            }
            size_t const rank = kv::bit_rank(bm, idx);
            bytes32_t out{};
            if (rec[kv::PG_FLAG] == 0) {
                std::memcpy(out.bytes, rec + kv::PG_PAYLOAD + rank * 32, 32);
                return out;
            }
            uint64_t ext_ref; // out-of-line raw value page; one more read
            std::memcpy(&ext_ref, rec + kv::PG_PAYLOAD, sizeof(ext_ref));
            unsigned char ext[kv::NODE_SIZE];
            read_page(ext_ref, ext);
            std::memcpy(out.bytes, ext + rank * 32, 32);
            return out;
        }
        return bytes32_t{}; // page not present
    }

    // ── blobs + code (same root-page shape) ─────────────────────────────────
    // Blob/code root-page layout; MUST match TrieDb::CODE_*.
    static constexpr size_t B_LEN = 8; // u64 total length
    static constexpr size_t B_NCHILD = 16; // u32 child count (index form)
    static constexpr size_t B_CHILDREN = 24; // u64 child refs (index form)
    static constexpr size_t B_INLINE = 16; // inline payload

    // Reassemble a blob / code value from its root page: inline (one page) or an
    // index page pointing at raw data pages. Empty when `root` is NULL_REF.
    void read_blob(uint64_t const root, byte_string &out) const
    {
        out.clear();
        if (root == kv::NULL_REF) {
            return;
        }
        append_blob(root, out);
    }

    // Append the bytes under `root`: raw data pages at height 0 (pg[1]), index
    // pages of the level below above it. Each level's length field covers just
    // its own range.
    void append_blob(uint64_t const root, byte_string &out) const
    {
        unsigned char pg[kv::NODE_SIZE];
        read_page(root, pg);
        uint64_t len;
        std::memcpy(&len, pg + B_LEN, 8);
        if (pg[0] == kv::N_BLOB_INLINE || pg[0] == kv::N_CODE_INLINE) {
            out.append(pg + B_INLINE, pg + B_INLINE + len);
            return;
        }
        MONAD_ASSERT(pg[0] == kv::N_BLOB_INDEX || pg[0] == kv::N_CODE_INDEX);
        uint8_t const height = pg[1];
        uint32_t nc;
        std::memcpy(&nc, pg + B_NCHILD, 4);
        std::vector<uint64_t> refs(nc); // snapshot before reading children
        std::memcpy(refs.data(), pg + B_CHILDREN, nc * 8);
        size_t const want = out.size() + len;
        out.reserve(want);
        unsigned char d[kv::NODE_SIZE];
        for (uint32_t i = 0; i < nc && out.size() < want; ++i) {
            if (height == 0) {
                read_page(refs[i], d);
                size_t const take =
                    std::min<size_t>(kv::NODE_SIZE, want - out.size());
                out.append(d, d + take);
            }
            else {
                append_blob(refs[i], out);
            }
        }
    }

    // A per-block blob category root, from the block-root tail. NULL_REF when
    // absent, including a pre-blob block whose root is a plain N_INTERNAL.
    uint64_t blob_root(uint64_t const block_root, size_t const cat) const
    {
        if (cat >= kv::BLOB_N || block_root == kv::NULL_REF) {
            return kv::NULL_REF;
        }
        unsigned char pg[kv::NODE_SIZE];
        read_page(block_root, pg);
        if (pg[0] != kv::N_BLOCK_ROOT) {
            return kv::NULL_REF;
        }
        uint64_t r;
        std::memcpy(&r, pg + kv::BLOCK_ROOT_BLOB_OFF + cat * 8, 8);
        return r;
    }

    // Number of entries in a per-tx table (N_BLOB_TABLE); -1 if the category is
    // absent or its root is not a table. The RPC also wants this (how many txs
    // a block's receipts / transactions / call frames cover).
    int64_t table_count(uint64_t const table_root) const
    {
        if (table_root == kv::NULL_REF) {
            return -1;
        }
        unsigned char pg[kv::NODE_SIZE];
        read_page(table_root, pg);
        if (pg[0] != kv::N_BLOB_TABLE) {
            return -1;
        }
        uint16_t count;
        std::memcpy(&count, pg + 2, sizeof(count));
        return static_cast<int64_t>(count);
    }

    // One entry of a per-tx table (N_BLOB_TABLE): entry i -> that tx's blob
    // root. Above height 0 (pg[1]) the table is a fixed-fan-out tree, so the
    // entry is reached by radix decomposition on the per-child span the node
    // itself records: descend to child i / span, then look for i % span in it.
    uint64_t table_entry(uint64_t const table_root, uint32_t const i) const
    {
        uint64_t root = table_root;
        uint32_t idx = i;
        for (;;) {
            if (root == kv::NULL_REF) {
                return kv::NULL_REF;
            }
            unsigned char pg[kv::NODE_SIZE];
            read_page(root, pg);
            if (pg[0] != kv::N_BLOB_TABLE) {
                return kv::NULL_REF;
            }
            uint16_t count;
            std::memcpy(&count, pg + 2, sizeof(count));
            if (idx >= count) {
                return kv::NULL_REF; // past the end of this range
            }
            if (pg[1] == 0) {
                uint64_t r;
                std::memcpy(
                    &r, pg + kv::HDR + static_cast<size_t>(idx) * 8, 8);
                return r;
            }
            // The node says how many entries one child covers, so the descent
            // does not depend on the fan-out the writer used.
            uint32_t span;
            std::memcpy(&span, pg + 4, sizeof(span));
            MONAD_ASSERT(span != 0);
            std::memcpy(
                &root, pg + kv::HDR + (static_cast<size_t>(idx) / span) * 8, 8);
            idx %= span;
        }
    }

    // Code by hash from the global content-addressed code tree. No hazard is
    // needed: the code tree is grow-only, so its pages are never reclaimed and a
    // momentarily stale root is still safe to walk (it can only lack the very
    // newest code, never point at freed pages).
    bool lookup_code(unsigned char const *const hash, byte_string &out)
    {
        RStore st{this};
        unsigned char v[8];
        uint64_t const root =
            __atomic_load_n(&meta_->code_tree_root, __ATOMIC_SEQ_CST);
        if (root == kv::NULL_REF ||
            !kv::blockmap::lookup(st, root, hash, 32, 8, v)) {
            return false;
        }
        uint64_t cref;
        std::memcpy(&cref, v, 8);
        read_blob(cref, out);
        return true;
    }

    // ── global hash indexes (transient hazard) ──────────────────────────────
    // Resolve a key in a cumulative hash index. Unlike the code tree these are
    // COW B+trees whose superseded roots ARE reclaimed, so the walk runs under a
    // transient pin on its own slot: pin the root, confirm it is still current,
    // walk, release. Resolution-only and pre-pin, so nothing stays pinned.
    bool index_lookup(
        uint64_t const &root_field, unsigned char const *const key,
        size_t const kl, size_t const vl, unsigned char *const out)
    {
        uint32_t const slot = haz_.acquire();
        bool found = false;
        for (;;) {
            uint64_t const root =
                __atomic_load_n(&root_field, __ATOMIC_SEQ_CST);
            haz_.publish1(slot, root);
            if (__atomic_load_n(&root_field, __ATOMIC_SEQ_CST) != root) {
                continue; // root advanced before the pin took; re-pin
            }
            if (root != kv::NULL_REF) {
                RStore st{this};
                found = kv::blockmap::lookup(st, root, key, kl, vl, out);
            }
            break;
        }
        haz_.release(slot);
        return found;
    }

    bool resolve_tx_hash(
        unsigned char const *const hash, uint64_t &block, uint32_t &tx_index)
    {
        unsigned char v[12]; // (block 8B, tx_index 4B)
        if (!index_lookup(meta_->txhash_index_root, hash, 32, 12, v)) {
            return false;
        }
        std::memcpy(&block, v, 8);
        std::memcpy(&tx_index, v + 8, 4);
        return true;
    }

    bool resolve_block_hash(unsigned char const *const hash, uint64_t &number)
    {
        unsigned char v[8];
        if (!index_lookup(meta_->blockhash_index_root, hash, 32, 8, v)) {
            return false;
        }
        std::memcpy(&number, v, 8);
        return true;
    }

    // ── meta cursors (read authority for RPC's block tags) ──────────────────
    uint64_t finalized_block() const
    {
        return __atomic_load_n(&meta_->finalized_block, __ATOMIC_SEQ_CST);
    }
    uint64_t oldest_block() const
    {
        return __atomic_load_n(&meta_->oldest_block, __ATOMIC_SEQ_CST);
    }
    uint64_t proposed_block() const
    {
        return __atomic_load_n(&meta_->proposed_block, __ATOMIC_SEQ_CST);
    }
    uint64_t voted_block() const
    {
        return __atomic_load_n(&meta_->voted_block, __ATOMIC_SEQ_CST);
    }

    // One consistent snapshot of all four tag cursors, which is what RPC's
    // block-tag resolution needs (it takes finalized / voted / proposed
    // together). finalized and oldest are lone counters; proposed and voted are
    // (block, id) PAIRS, read under the seqlock exec publishes them with: an
    // odd counter means a write is in flight, and an unchanged counter across
    // the whole read means none landed during it.
    //
    // Re-reading a pair's own fields does NOT substitute for this, in either
    // store order: the two stores are not atomic as a unit, so the
    // first-written field can be observed paired with the other field's
    // PREVIOUS value while both reads of it agree. False => no stable snapshot;
    // the caller keeps whatever it had rather than acting on a torn pair.
    //
    // Times the read had to start over. Zero means the race never landed in a
    // run, NOT that the retry path works -- reported as such rather than
    // counted as coverage.
    mutable uint64_t tag_retries_{0};

    uint64_t tag_retries() const
    {
        return tag_retries_;
    }

    bool read_tags(
        uint64_t &finalized, uint64_t &earliest, uint64_t &proposed,
        unsigned char *const proposed_id, uint64_t &voted,
        unsigned char *const voted_id) const
    {
        for (int attempt = 0; attempt < 64; ++attempt) {
            if (attempt > 0) {
                ++tag_retries_;
            }
            uint64_t const s1 =
                __atomic_load_n(&meta_->tag_seq, __ATOMIC_SEQ_CST);
            if ((s1 & 1) != 0) {
                continue; // a publish is mid-flight
            }
            finalized = finalized_block();
            earliest = oldest_block();
            proposed = proposed_block();
            voted = voted_block();
            std::memcpy(proposed_id, meta_->proposed_id, 32);
            std::memcpy(voted_id, meta_->voted_id, 32);
            // The id copies are plain reads, so nothing above stops the
            // compiler sinking them PAST the validating load below -- an
            // acquire load constrains what moves before it, not earlier
            // accesses moving after it. Without this fence the check reads a
            // counter that the payload was fetched after, and accepts torn
            // pairs: at -O3 gcc does exactly that (36,748 torn in KVDB_TAGTEST,
            // zero at -O2).
            std::atomic_thread_fence(std::memory_order_acquire);
            if (__atomic_load_n(&meta_->tag_seq, __ATOMIC_SEQ_CST) == s1) {
                return true;
            }
        }
        return false;
    }
};

// C++ shims called by the RPC FFI (rust/crates/monad-triedb/src/ffi.cpp). Keep
// KvReader's definition (and the file-local kv:: internals it uses) in this TU.
KvReader *kv_reader_open(char const *const kvhdr_path)
{
    auto *const r = new KvReader{};
    if (!r->open(kvhdr_path)) {
        r->close();
        delete r;
        return nullptr;
    }
    return r;
}

void kv_reader_close(KvReader *const r)
{
    if (r != nullptr) {
        r->close();
        delete r;
    }
}

int64_t kv_reader_protect_block(
    KvReader *const r, uint64_t const block, unsigned char const *const id)
{
    return r->protect_block(block, id);
}

void kv_reader_end_protect(KvReader *const r, int64_t const handle)
{
    r->end_protect(handle);
}

bool kv_reader_account(
    KvReader *const r, int64_t const handle, unsigned char const *const addr,
    unsigned char *const out_balance_be, unsigned char *const out_code_hash,
    uint64_t *const out_nonce)
{
    Account a;
    uint64_t sref = 0;
    if (!r->find_account(r->handle_root(handle), addr, a, sref)) {
        return false;
    }
    // Balance crosses the FFI as 32B big-endian (not the native little-endian
    // limbs), so Rust never depends on the C++ uint256 layout.
    store_be(out_balance_be, a.balance);
    std::memcpy(out_code_hash, a.code_hash.bytes, 32);
    *out_nonce = a.nonce;
    return true;
}

void kv_reader_storage(
    KvReader *const r, int64_t const handle, unsigned char const *const addr,
    unsigned char const *const key, unsigned char *const out32)
{
    bytes32_t k{};
    std::memcpy(k.bytes, key, 32);
    bytes32_t const v = r->read_slot(r->handle_root(handle), addr, k);
    std::memcpy(out32, v.bytes, 32);
}

// Blob / code results cross the FFI as a raw owned buffer + length, released
// with kv_reader_free -- the same new[]/delete[] convention triedb_read and
// triedb_finalize already use, so the caller frees one way for both backends.
namespace
{
    bool kv_hand_out(
        byte_string const &v, unsigned char const **const out,
        uint64_t *const out_len)
    {
        *out_len = v.size();
        if (v.empty()) {
            *out = nullptr; // nothing to free; kv_reader_free(nullptr) is a no-op
            return true;
        }
        auto *const buf = new unsigned char[v.size()];
        std::memcpy(buf, v.data(), v.size());
        *out = buf;
        return true;
    }
}

bool kv_reader_code(
    KvReader *const r, unsigned char const *const code_hash,
    unsigned char const **const out, uint64_t *const out_len)
{
    byte_string v;
    if (!r->lookup_code(code_hash, v)) {
        return false;
    }
    return kv_hand_out(v, out, out_len);
}

bool kv_reader_block_blob(
    KvReader *const r, int64_t const handle, uint32_t const category,
    unsigned char const **const out, uint64_t *const out_len)
{
    uint64_t const br = r->blob_root(r->handle_root(handle), category);
    if (br == ~uint64_t{0}) {
        return false;
    }
    byte_string v;
    r->read_blob(br, v);
    return kv_hand_out(v, out, out_len);
}

bool kv_reader_blob_present(
    KvReader *const r, int64_t const handle, uint32_t const category)
{
    return r->blob_root(r->handle_root(handle), category) != ~uint64_t{0};
}

int64_t kv_reader_table_count(
    KvReader *const r, int64_t const handle, uint32_t const category)
{
    uint64_t const t = r->blob_root(r->handle_root(handle), category);
    return r->table_count(t);
}

bool kv_reader_tx_blob(
    KvReader *const r, int64_t const handle, uint32_t const category,
    uint32_t const tx_index, unsigned char const **const out,
    uint64_t *const out_len)
{
    uint64_t const table = r->blob_root(r->handle_root(handle), category);
    uint64_t const br = r->table_entry(table, tx_index);
    if (br == ~uint64_t{0}) {
        return false;
    }
    byte_string v;
    r->read_blob(br, v);
    return kv_hand_out(v, out, out_len);
}

void kv_reader_free(unsigned char const *const p)
{
    delete[] p; // matches kv_hand_out's new unsigned char[]; nullptr is a no-op
}

bool kv_reader_resolve_tx_hash(
    KvReader *const r, unsigned char const *const hash,
    uint64_t *const out_block, uint32_t *const out_tx_index)
{
    return r->resolve_tx_hash(hash, *out_block, *out_tx_index);
}

bool kv_reader_resolve_block_hash(
    KvReader *const r, unsigned char const *const hash,
    uint64_t *const out_number)
{
    return r->resolve_block_hash(hash, *out_number);
}

uint64_t kv_reader_cursor(KvReader *const r, int const which)
{
    switch (which) {
    case 0:
        return r->finalized_block();
    case 1:
        return r->oldest_block();
    case 2:
        return r->proposed_block();
    default:
        return r->voted_block();
    }
}

bool kv_reader_tags(
    KvReader *const r, uint64_t *const finalized, uint64_t *const earliest,
    uint64_t *const proposed, unsigned char *const proposed_id,
    uint64_t *const voted, unsigned char *const voted_id)
{
    return r->read_tags(
        *finalized, *earliest, *proposed, proposed_id, *voted, voted_id);
}

uint64_t kv_reader_tag_retries(KvReader *const r)
{
    return r->tag_retries();
}
#endif // KVDB_PROTO

MONAD_NAMESPACE_END
