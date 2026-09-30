// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/execution/ethereum/db/offset_trie.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/nibble.h>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <new>
#include <optional>
#include <span>
#include <utility>
#include <vector>
#ifdef MONAD_ZKVM_KECCAK_SITES
#include <category/core/keccak_sites.hpp>
#else
#define MONAD_KECCAK_SITE(s, len) ((void)0)
#endif

MONAD_MPT_NAMESPACE_BEGIN

NodeId OffsetTrie::read_root(byte_string_view const blob)
{
    unsigned char const *const base = blob.data();
    size_t const len = blob.size();
    MONAD_ASSERT(len >= HEADER_LEN);
    MONAD_ASSERT(
        base[0] == 'M' && base[1] == 'Z' && base[2] == 'W' && base[3] == 0x01);
    // Keep blob offsets and overlay ids in disjoint halves of the NodeId
    // space (blob < OVERLAY_BASE, fresh ids >= OVERLAY_BASE). Bounding the
    // blob size bounds every offset. Real witnesses are ~MBs; this only
    // rejects a pathological >=2 GiB blob.
    MONAD_ASSERT(len < OVERLAY_BASE);
    NodeId const root = read_node_id(base + 4);
    MONAD_ASSERT(
        root == NULL_ID || (static_cast<uint64_t>(root) >= HEADER_LEN &&
                            static_cast<uint64_t>(root) < len));
    return root;
}

OffsetTrie::OffsetTrie(byte_string_view const blob)
    : blob_(blob)
    // Declaration order puts this before `root`, so it is formed before
    // read_root's asserts run. If the blob is shorter than the header this
    // wraps and read_root aborts on the next initialiser, before any lookup
    // can observe it.
    , blob_span_{blob_.size() - HEADER_LEN}
    , root{read_root(blob_)}
{
    unsigned char const *const base = blob_.data();

    // Prime hashes bottom-up over the blob's nodes (children precede
    // parents), rejecting any node whose extent leaves the region.
    unsigned char const *const region_end = blob_.end();
    uint64_t node_offset = HEADER_LEN;
    NodeViewBase node{base + node_offset};
    // The only node carrying the EMPTY tag is the magic header at the NULL_ID
    // offset, which this walk starts past. checked_end has no EMPTY arm, so
    // encountering that tag in the blob data aborts as an invalid tag. However,
    // we have to check the very first node isn't EMPTY (provided it exists).
    MONAD_ASSERT(node.bytes() == region_end || node.tag() != EMPTY);
    // One BYTE per blob offset, not one bit. The bitmap cost a
    // read-modify-write to set -- shift, scale, add, load, bset, store -- and
    // the same shape to test; a byte array is an add and a store to set, an add
    // and a load to test. Six instructions become three on each side.
    //
    // No alignment assumption: indexed by the raw offset, so it holds whatever
    // the blob's node sizes produce. The price is the zeroing, and it is not
    // close -- the extra bytes are one memset, which ZisK charges per 8-byte
    // word on the aligned path, against six instructions saved per lookup at 68
    // COST a step.
#if defined(MONAD_ZKVM_ZISK)
    // No explicit zeroing is needed on ZisK: the guest's bump allocator never
    // reuses memory, and ZisK's memory constraints guarantee that unwritten
    // addresses read as zero. Unmarked offsets therefore still fail
    // validation.
    // free is a no-op on this guest, so no deallocation is needed.
    std::span<unsigned char> const node_offsets{
        static_cast<unsigned char *>(::operator new(blob_.size())),
        blob_.size()};
    claim_marks_ = node_offsets.data();
#else
    std::vector<unsigned char> node_offsets(blob_.size(), 0);
#endif
    // Carried as a pointer, not indexed. The DIGEST arm below is nine nodes in
    // ten and its only use of the offset is this one subscript, so an index
    // costs the scale-and-add on every one of them
    // -- `add` then `sb` -- plus its own increment. A pointer is the store and
    // the increment, and the offset itself is then only wanted on the general
    // path, where it is one `sub` per node.
    //
    // Invariant, established here and maintained by both arms:
    //     seen == node_offsets.data() + (node.bytes() - base)
    unsigned char *seen = node_offsets.data() + node_offset;

    // Sized before the sweep fills it. unordered_dense rehashes on growth, and
    // a rehash recomputes the hash of every entry it already holds and moves it
    // -- so a map that doubles its way to fifteen thousand entries hashes them
    // about twice over. Nine nodes in ten carry the DIGEST tag and are never
    // hashed, and of the rest only those whose canonical RLP reaches 32 bytes
    // are, which on the corpus is one entry per 430 blob bytes. The divisor
    // below is deliberately below that: over-reserving costs arena, which this
    // guest has, and under-reserving costs the rehash this is here to avoid.
#if defined(MONAD_ZKVM_ZISK)
    // The hash tables in place of the map: one slot per four blob bytes, one
    // per fresh id, and a first chunk of entries sized as the map's reserve.
    blob_hash_slots_ = static_cast<CachedHash **>(
        ::operator new((blob_.size() / 4 + 1) * sizeof(CachedHash *)));
    fresh_hash_slots_ = static_cast<CachedHash **>(
        ::operator new(FRESH_HASH_SLOTS * sizeof(CachedHash *)));
    refill_hash_pool(blob_.size() / 256 + 1);
#else
    hashes_.reserve(blob_.size() / 256);
#endif
#if defined(MONAD_ZKVM_ZISK)
    blob_overlay_slots_ = static_cast<byte_string **>(
        ::operator new((blob_.size() / 4 + 1) * sizeof(byte_string *)));
    fresh_overlay_slots_ = static_cast<byte_string **>(
        ::operator new(FRESH_HASH_SLOTS * sizeof(byte_string *)));
#else
    // Reserve initial overlay capacity to avoid early rehashes.
    // The number of nodes created during commit is not known yet.
    overlay_.reserve(1024);
#endif

    // A node's byte is set when the walk reaches it and cleared when a parent
    // claims it as a child.
    // A child whose byte is clear is either previously unseen/invalid or
    // already claimed by a different parent.
    //
    // Count unread bytes plus DIGEST_NODE_LEN per marked, unclaimed node.
    // Reading a node replaces its encoded length with DIGEST_NODE_LEN;
    // claiming it subtracts DIGEST_NODE_LEN. DIGEST nodes need no adjustment.
    // Once the region is fully read and root claimed, zero means no orphan
    // remains, without scanning node_offsets again.
    size_t unclaimed = static_cast<size_t>(region_end - node.bytes());

#if !defined(MONAD_ZKVM_ZISK)
    // Reuse one CachedHash for the sweep: Keccak overwrites the hash directly,
    // avoiding per-node zeroing and an intermediate copy. All entries are
    // valid.
    CachedHash ch{};
    ch.valid = true;
#endif

    // Read once: the byte stores below may alias anything, so gcc reloads a
    // member after each of them, twice a child pair.
    size_t const blob_size = blob_.size();
    auto const is_valid_offset = [&](NodeId c) {
        if (c == NULL_ID) {
            return;
        }
        uint64_t child_offset = static_cast<uint64_t>(c);
        MONAD_ASSERT(
            child_offset < blob_size && node_offsets[child_offset] != 0);
        node_offsets[child_offset] = 0;
        unclaimed -= DIGEST_NODE_LEN;
    };
#if !defined(MONAD_ZKVM_ZISK)
    unsigned char rlp_buf[MAX_NODE_RLP];
#endif

    while (node.bytes() < region_end) {
        // In range by the loop's own condition: the walk runs while
        // node.bytes() < region_end, so node_offset is an offset into the
        // blob and never one past its end.
        MONAD_DEBUG_ASSERT(node_offset < blob_.size());
        if (node.tag() == DIGEST) {
            // Check the extent before advancing either pointer past the node.
            MONAD_ASSERT(
                static_cast<size_t>(region_end - node.bytes()) >=
                DIGEST_NODE_LEN);
            *seen = 1;
            seen += DIGEST_NODE_LEN;
            node = NodeViewBase{node.bytes() + DIGEST_NODE_LEN};
            continue;
        }
        // Wanted from here down -- by the hash key and by the marking below
        // -- and nowhere in the arm above.
        node_offset = static_cast<uint64_t>(node.bytes() - base);

        // checked_end asserts that the current node does not reach past the end
        // of the region
        auto next_offset =
            static_cast<uint64_t>(node.checked_end(region_end) - base);
#if defined(MONAD_ZKVM_ZISK)
        // Read once: the copy of a branch's children may alias the blob, so
        // gcc would read the tag again to choose the priming encode.
        Tag const tag = node.tag();
#endif

        match(
            node,
            Cases{
                [&](BranchView b) {
                    // Validate the 16 children two at a time: a uint64_t load
                    // spans exactly one pair, low word first. Unrolled in full:
                    // a turn's counter and test would be two steps a pair.
                    static_assert(std::endian::native == std::endian::little);
                    static_assert(
                        sizeof(uint64_t) == 2 * sizeof(node_id_wire_t));
#if defined(MONAD_ZKVM_ZISK)
                    // One aligned copy of the children, which the priming
                    // encode below validates -- it claims each child where it
                    // first reads it, before reading anything of the child's.
                    std::memcpy(
                        primed_slots_ + PRIMED_CHILDREN,
                        b.payload(),
                        16 * sizeof(node_id_wire_t));
#else
                    unsigned char const *const p = b.payload();
                    uint64_t pair;
#pragma GCC unroll 8
                    for (unsigned i = 0; i < 8; ++i) {
                        std::memcpy(&pair, p + i * sizeof(pair), sizeof(pair));
                        is_valid_offset(
                            NodeId{static_cast<node_id_wire_t>(pair)});
                        is_valid_offset(
                            NodeId{static_cast<node_id_wire_t>(pair >> 32)});
                    }
#endif
                },
                [&](ExtView e) { is_valid_offset(e.child()); },
                [&](AccountLeafView a) { is_valid_offset(a.storage()); },
                [](auto) {}});

        // checked_end has rejected every other tag and the arm above takes the
        // digests: the node is a branch, an extension or a leaf, and primed.
#if defined(MONAD_ZKVM_ZISK)
        // Encoded where a hashed node keeps it: see CachedHash::rlp. An
        // inlined node's window is reused.
        if (MONAD_UNLIKELY(rlp_window_ == rlp_windows_end_)) {
            refill_rlp_windows();
        }
        auto &window =
            *reinterpret_cast<unsigned char(*)[MAX_NODE_RLP]>(rlp_window_);
        node_rlp_span const rem =
            tag == BRANCH
                ? encode_rlp<true, true>(
                      node,
                      node_rlp_span{window},
                      primed_slots_ + PRIMED_CHILDREN)
                : encode_rlp<true>(node, node_rlp_span{window}); // priming pass
#else
        node_rlp_span const rem =
            encode_rlp<true>(node, node_rlp_span{rlp_buf}); // priming pass
#endif
        // Marked and advanced before the hash, which ends the turn: the
        // offsets die before the call instead of living across it.
        node_offsets[node_offset] = 1;
        unclaimed = unclaimed + DIGEST_NODE_LEN - (next_offset - node_offset);
        node = NodeViewBase{base + next_offset};
        seen = node_offsets.data() + next_offset;
        // Only hash-referenced nodes (canonical RLP >= 32 B) are cached;
        // smaller nodes are inlined by their parent, so caching their hash
        // would make child_ref emit a 32-byte ref where the trie inlines it.
        if (rem.rlp_size() >= 32) {
            MONAD_KECCAK_SITE(TRIE_PRIME, rem.rlp_size());
#if defined(MONAD_ZKVM_ZISK)
            // The sweep reaches each node once, so its slot is empty: the
            // digest goes straight into a new entry. Filled before the hash,
            // which comes last: nothing then lives across the call, where the
            // entry and the RLP's length were saved and reloaded around it.
            CachedHash *const e = new_hash_entry();
            e->valid = true;
            e->rlp = rem.base() + rem.size();
            e->rlp_len = rem.rlp_size();
            blob_hash_slots_[node_offset >> 2] = e;
            rlp_window_ += RLP_WINDOW_STRIDE;
            monad_keccak256(rem.rlp_data(), rem.rlp_size(), e->h.bytes);
#else
            monad_keccak256(rem.rlp_data(), rem.rlp_size(), ch.h.bytes);
            hashes_.insert_or_assign(NodeId{node_offset}, ch);
#endif
        }
    }
    MONAD_ASSERT(node.bytes() == region_end); // nodes tile exactly
    is_valid_offset(root);
#if defined(MONAD_ZKVM_ZISK)
    unclaimed -= claimed_bytes_;
    claim_marks_ = nullptr;
#endif

    // Any remaining count indicates a node unreachable from root.
    MONAD_ASSERT(unclaimed == 0);
}

NodeViewBase OffsetTrie::find_original(NodeId id, NibblesView key) const
{
    NodeViewBase found = empty();
    while (id != NULL_ID) {
        NodeViewBase const node = get_original(id);
        // Most levels are branches: tested first, where the match's compare
        // tree reaches them third.
        if (MONAD_LIKELY(node.tag() == BRANCH)) {
            if (key.nibble_size() == 0) { // no value at a branch
                break;
            }
            // The child is read after drop_front1, not between it and get(0):
            // gcc copies that stretch into both arms of the nibble's parity
            // test, and a child read there is widened where the arms meet, a
            // lw and two shifts for one lwu.
            unsigned const i = key.get(0);
            key.drop_front1();
            id = BranchView{node}.child(i);
            continue;
        }
        id = match(
            node,
            Cases{
                [](BranchView) -> NodeId { std::unreachable(); },
                [&](ExtView e) -> NodeId {
                    NibblesView const ep = e.path();
                    if (!key.starts_with(ep)) {
                        return NULL_ID;
                    }
                    key = key.substr(ep.nibble_size());
                    return e.child();
                },
                [&](AccountLeafView l) -> NodeId {
                    if (l.path() == key) {
                        found = l;
                    }
                    return NULL_ID;
                },
                [&](StorageLeafView l) -> NodeId {
                    if (l.path() == key) {
                        found = l;
                    }
                    return NULL_ID;
                },
                [](DigestView) -> NodeId {
                    MONAD_ABORT("incomplete witness: lookup hit a Digest");
                },
                [](NullView) -> NodeId {
                    // There is only a single NullView node, namely the NULL_ID
                    // magic header. However, since id is strictly greater than
                    // 0 inside the loop, get_original can never reach it.
                    MONAD_ABORT("malformed trie: node not found");
                },
            });
    }
    return found;
}

bytes32_t OffsetTrie::hash(NodeId const id)
{
    auto const node = get_current(id);
    return match(
        node,
        Cases{
            [](NullView) { return NULL_ROOT; },
            [](DigestView d) { return d.hash(); },
            [&](auto) {
                if (auto const *const hit = cached_hash(id)) {
                    return *hit;
                }

                alignas(8) unsigned char buf[MAX_NODE_RLP];
                node_rlp_span const rem = encode_current(id, node, buf);
                MONAD_ASSERT(rem.rlp_size() >= 32);
                bytes32_t h;
                // RLP occupies the tail: [rem.end(), buf_end).
                MONAD_KECCAK_SITE(TRIE_PRIME, rem.rlp_size());
                monad_keccak256(rem.rlp_data(), rem.rlp_size(), h.bytes);

                store_hash(id, h);
                return h;
            }});
}

bytes32_t OffsetTrie::state_root()
{
    return hash(root);
}

#if defined(MONAD_ZKVM_ZISK)
void OffsetTrie::refill_hash_pool(size_t const entries)
{
    // Never freed, and never moved: an entry's address stays its slot's.
    hash_pool_ =
        static_cast<CachedHash *>(::operator new(entries * sizeof(CachedHash)));
    hash_pool_end_ = hash_pool_ + entries;
}

void OffsetTrie::refill_rlp_windows()
{
    // Never freed, and never moved: a kept RLP stays where its entry says.
    constexpr size_t WINDOWS = 2048;
    rlp_window_ = static_cast<unsigned char *>(
        ::operator new(WINDOWS * RLP_WINDOW_STRIDE));
    rlp_windows_end_ = rlp_window_ + WINDOWS * RLP_WINDOW_STRIDE;
}

namespace
{
    // The length of a node's RLP list header: its payload is under 2^16.
    constexpr size_t rlp_list_header_len(unsigned char const b)
    {
        return b <= 0xf7 ? 1 : static_cast<size_t>(b - 0xf6);
    }

    // A child ref: the empty string, a 32-byte hash, or an inlined node,
    // which is under 32 bytes and so a short list.
    constexpr size_t rlp_ref_len(unsigned char const b)
    {
        return b == 0x80 ? 1
               : b == 0xa0 ? 1 + KECCAK256_SIZE
                           : 1 + static_cast<size_t>(b - 0xc0);
    }

    // A compact path: a single byte that is its own RLP, or a short string.
    constexpr size_t rlp_path_len(unsigned char const b)
    {
        return b < 0x80 ? 1 : 1 + static_cast<size_t>(b - 0x80);
    }
}

// The node's bytes are the ones it was primed with, so its RLP differs from
// the priming RLP only in the refs of the children a descent has passed
// through since -- which set their bits in `dirty` -- and each of those is
// recomputed and written over its ref, in the window itself: `dirty` never
// clears, so every patch rewrites all of them, and a ref is only written when
// its length holds. A ref whose length changed would move everything after
// it: that case, zero, falls back to a full encode.
size_t OffsetTrie::patch_rlp(CachedHash const &e, NodeViewBase const node)
{
    size_t const len = e.rlp_len;
    unsigned char *const out = e.rlp;
    unsigned char *p = out + rlp_list_header_len(out[0]);
    uint64_t mask = e.dirty;
    if (node.tag() == BRANCH) {
        BranchView const b{node};
        // Each dirty child's ref starts where the priming encode recorded it,
        // in the window's head. A dirty child is never a digest or empty, so
        // its offset is recorded: zero would be a slot never written.
        unsigned char *const window = e.rlp + len - MAX_NODE_RLP;
        uint64_t const *const starts =
            reinterpret_cast<uint64_t const *>(window);
        while (mask != 0) {
            unsigned const k = static_cast<unsigned>(std::countr_zero(mask));
            mask &= mask - 1;
            size_t const at = starts[k];
            if (at == 0) {
                return 0;
            }
            unsigned char *const ref = window + at;
            if (!patch_ref(b.child(k), ref, rlp_ref_len(*ref))) {
                return 0;
            }
        }
    }
    else {
        MONAD_ASSERT(node.tag() == EXT);
        p += rlp_path_len(*p);
        if ((mask & 1) != 0 && !patch_ref(ExtView{node}.child(), p, rlp_ref_len(*p))) {
            return 0;
        }
    }
    return len;
}

bool OffsetTrie::patch_ref(
    NodeId const child, unsigned char *const ref, size_t const ref_len)
{
    // A hash ref over a child that still hashes, the common case: the digest
    // goes straight over the old one -- ref[0] stays 0xa0 -- and into the
    // child's entry straight from Keccak, where child_ref would copy it into
    // the entry, into a ref of its own, and that ref over this one.
    if (ref_len == HASH_RLP_LEN) {
        // The commonest child: a primed branch or extension the block has
        // not rewritten, below a dirty ref. Its slots are read once, and its
        // RLP is its patched priming RLP -- what encode_current would build
        // after reading the same slots again. A patch that falls back to the
        // full encode leaves it to the general path below.
        uint64_t const v = static_cast<uint64_t>(child);
        if (v < OVERLAY_BASE) {
            NodeViewBase const original = get_original(child);
            Tag const tag = original.tag();
            CachedHash *const e = blob_hash_slots_[v >> 2];
            if (blob_overlay_slots_[v >> 2] == nullptr &&
                (tag == BRANCH || tag == EXT) && e != nullptr &&
                e->rlp != nullptr) {
                auto const patched = [&] {
                    size_t const len = patch_rlp(*e, original);
                    if (len == 0) {
                        return false;
                    }
                    MONAD_KECCAK_SITE(TRIE_ENCODE, len);
                    monad_keccak256(e->rlp, len, e->h.bytes);
                    e->valid = true;
                    return true;
                };
                if (e->valid || patched()) {
                    std::memcpy(ref + 1, e->h.bytes, KECCAK256_SIZE);
                    return true;
                }
            }
        }
        NodeViewBase const node = get_current(child);
        Tag const tag = node.tag();
        if (tag == BRANCH || tag == EXT || tag == LEAF_ACCT ||
            tag == LEAF_STORAGE) {
            if (bytes32_t const *const hit = cached_hash(child)) {
                std::memcpy(ref + 1, hit->bytes, KECCAK256_SIZE);
                return true;
            }
            alignas(8) unsigned char buf[MAX_NODE_RLP];
            node_rlp_span const rem = encode_current(child, node, buf);
            if (rem.rlp_size() < 32) {
                return false; // now inlined: the ref's length changes
            }
            CachedHash *&slot = hash_slot(child);
            if (slot == nullptr) {
                slot = new_hash_entry();
            }
            MONAD_KECCAK_SITE(TRIE_ENCODE, rem.rlp_size());
            monad_keccak256(rem.rlp_data(), rem.rlp_size(), slot->h.bytes);
            slot->valid = true;
            std::memcpy(ref + 1, slot->h.bytes, KECCAK256_SIZE);
            return true;
        }
    }
    unsigned char tmp[MAX_NODE_RLP];
    node_rlp_span const rem = child_ref<false>(child, node_rlp_span{tmp});
    if (rem.rlp_size() != ref_len) {
        return false;
    }
    std::memcpy(ref, rem.rlp_data(), ref_len);
    return true;
}
#endif

OffsetTrie::node_rlp_span OffsetTrie::encode_current(
    NodeId const id, NodeViewBase const node,
    unsigned char (&buf)[MAX_NODE_RLP])
{
#if defined(MONAD_ZKVM_ZISK)
    // A primed node that is neither fresh nor rewritten: a blob id with no
    // overlay entry, its slot bounded by the get_current or get_original that
    // produced `node`. Only branches and extensions have children to patch.
    uint64_t const v = static_cast<uint64_t>(id);
    if (v < OVERLAY_BASE && blob_overlay_slots_[v >> 2] == nullptr &&
        (node.tag() == BRANCH || node.tag() == EXT)) {
        CachedHash const *const e = blob_hash_slots_[v >> 2];
        if (e != nullptr && e->rlp != nullptr) {
            if (size_t const len = patch_rlp(*e, node); len != 0) {
                // Patched where it is kept: the window is an RLP buffer like
                // `buf`, its RLP ending at the same place.
                auto &window = *reinterpret_cast<unsigned char(*)[MAX_NODE_RLP]>(
                    e->rlp + len - MAX_NODE_RLP);
                return node_rlp_span{window}.shrink(len);
            }
        }
    }
#else
    (void)id;
#endif
    return encode_rlp(node, node_rlp_span{buf});
}

template <bool priming_pass>
OffsetTrie::node_rlp_span OffsetTrie::child_ref_compute(
    NodeId const id, NodeViewBase const node, OffsetTrie::node_rlp_span dest)
{
    alignas(8) unsigned char buf[MAX_NODE_RLP];
    node_rlp_span const rem = [&] {
        if constexpr (priming_pass) {
            return encode_rlp<true>(node, node_rlp_span{buf});
        }
        else {
            return encode_current(id, node, buf);
        }
    }();
    unsigned char const *const child_rlp = rem.rlp_data();
    size_t const child_rlp_len = rem.rlp_size();
    if (child_rlp_len < 32) {
        std::memcpy(dest.last(child_rlp_len).data(), child_rlp, child_rlp_len);
        return dest.shrink(child_rlp_len);
    }
    // Unreachable: the sweep validates that children were already seen and
    // caches hash-referenced nodes before their parents. Hashing in blob order
    // avoids recursive traversal without duplicating the later pass's work.
    if constexpr (priming_pass) {
        MONAD_ABORT("offset trie: unprimed hash-referenced node (bad offset)");
    }
    bytes32_t h;
    MONAD_KECCAK_SITE(TRIE_ENCODE, child_rlp_len);
    monad_keccak256(child_rlp, child_rlp_len, h.bytes);
    store_hash(id, h);
    return encode_rlp(h, dest);
}

namespace
{
    // Like rlp::zeroless_view for a 32-byte big-endian value, but skips
    // leading zeros eight bytes at a time. Reads the aligned stack copy
    // because unaligned word reads from the blob are more expensive on ZisK.
    [[gnu::always_inline]] inline byte_string_view
    zeroless_view32(unsigned char const *const p)
    {
        for (unsigned w = 0; w < 32; w += 8) {
            uint64_t const word = bits::load64(p + w);
            if (word == 0) {
                continue;
            }
            // `word` holds p[w..w+7] little-endian, so a leading zero byte in
            // memory order is a low-order zero byte here.
#if defined(__riscv_zbb) || defined(__x86_64__) || defined(__aarch64__)
            unsigned const lz =
                static_cast<unsigned>(std::countl_zero(std::byteswap(word))) /
                8;
#else
            unsigned const lz =
                static_cast<unsigned>(bits::clz64(bits::bswap64(word))) / 8;
#endif
            return {p + w + lz, 32 - w - lz};
        }
        return {p + 32, 0};
    }
}

template <bool priming_pass, bool claims>
OffsetTrie::node_rlp_span
OffsetTrie::encode_rlp(
    NodeViewBase const node, OffsetTrie::node_rlp_span dest,
    [[maybe_unused]] node_id_wire_t const *const children_in)
{
    MONAD_DEBUG_ASSERT(node.tag() != EMPTY && node.tag() != DIGEST);
    if constexpr (claims) {
        // The constructor hands the claims pass its branches only: the other
        // arms, their buffers in the frame and the dispatch compile away.
        if (node.tag() != BRANCH) {
            std::unreachable();
        }
    }
    // Compact-encode `path` straight into d's tail as an RLP string; return
    // d shrunk. The compact form is clen = nibble_size/2 + 1 bytes (<= 33,
    // always a short string): write it directly, then prepend the
    // 0x80+path_len prefix. When path_len == 1 the single byte is <= 0x3F,
    // so it is already its own RLP and no prefix is added.
    auto const encode_path = [](OffsetTrie::node_rlp_span d,
                                NibblesView const path,
                                bool const terminating) {
        size_t const path_len = path.nibble_size() / 2 + 1;
        compact_encode_raw(d.last(path_len).data(), path, terminating);
        d = d.shrink(path_len);
        if (path_len > 1) {
            d.back() = zx(0x80 + path_len);
            d = d.shrink(1);
        }
        return d;
    };
    // Prepend the list header for payload [s.end(), dest.end()); return the
    // final span.
    //
    // Node payloads need at most a three-byte RLP list prefix. Write it
    // directly to avoid generic length sizing and copying; zx keeps byte
    // stores cheap on ZisK.
    auto const wrap = [](OffsetTrie::node_rlp_span const s) {
        size_t const payload_len = s.rlp_size();
        if (payload_len <= 55) {
            s.back() = zx(0xC0 + payload_len);
            return s.shrink(1);
        }
        if (payload_len <= 0xFF) {
            auto const hdr = s.last(2);
            hdr[0] = zx(0xF8);
            hdr[1] = zx(payload_len);
            return s.shrink(2);
        }
        // Ensure the payload length fits in the two-byte field below.
        MONAD_ASSERT(payload_len <= 0xFFFF);
        auto const hdr = s.last(3);
        hdr[0] = zx(0xF9);
        hdr[1] = zx(payload_len >> 8);
        hdr[2] = zx(payload_len & 0xFF);
        return s.shrink(3);
    };
    return match(
        node,
        Cases{
            [&, wrap](BranchView b) -> node_rlp_span {
                dest.back() = zx(0x80); // empty branch value, last element
                dest = dest.shrink(1);
#if defined(MONAD_ZKVM_ZISK)
                alignas(8) node_id_wire_t own[16];
                node_id_wire_t const *children = children_in;
                if (children == nullptr) {
                    std::memcpy(own, b.payload(), sizeof(own));
                    children = own;
                }
#else
                std::array<node_id_wire_t, 16> const children = b.children();
#endif

                // A digest is pre-state only, put_node never shadows a digest
                // id and its original bytes are still its current bytes which
                // is why we can memcpy from the blob_ directly below.
                //
                // Taken widened. A wire field reaching a 64-bit parameter is
                // cheaper than a 32-bit one.
                //
                // Priming already validated all child IDs as blob offsets;
                // only mutation needs the overlay check. get_original also
                // checks bounds before access.
                // The blob's address, held: the mark and digest byte stores
                // below may alias any member, so gcc reloads blob_ after each.
                unsigned char const *const blob = blob_.data();
                auto const blob_digest_at = [&](uint64_t const w) {
                    if constexpr (priming_pass) {
                        // No bounds test: the priming pass encodes only nodes
                        // the constructor has walked, and each child was
                        // asserted zero or a node start the walk had marked
                        // before this read -- by the constructor, or, for a
                        // branch it walks, by this encode's claim above -- so
                        // at least HEADER_LEN and inside the blob.
                        return w != 0 && NodeViewBase{blob + w}.tag() ==
                                             Tag::DIGEST;
                    }
                    else {
                        return w != 0 &&
                               get_original(NodeId{w}).tag() == Tag::DIGEST;
                    }
                };
                auto const digest_at = [blob_digest_at](uint64_t const w) {
                    if constexpr (priming_pass) {
                        return blob_digest_at(w);
                    }
                    else {
                        return w < OVERLAY_BASE && blob_digest_at(w);
                    }
                };

#if defined(MONAD_ZKVM_ZISK)
                [[maybe_unused]] unsigned char *const marks = claim_marks_;
                [[maybe_unused]] size_t const blob_size = blob_.size();
                [[maybe_unused]] size_t claimed = 0;
                static_assert(DIGEST_NODE_LEN == HASH_RLP_LEN);
#endif
                // Walked by pointer: an index costs a shift and an add to
                // reach each slot, and a copy at the end of every turn.
                // Decremented after the test, not in it: `c-- != first` tests
                // the value before the decrement, which gcc keeps in a copy
                // every turn.
                //
                // An empty child's byte, zero-extended once and out of the
                // loop: zx inside it copies the hoisted constant into a new
                // register every turn. Not const: a const byte with a constant
                // initialiser is a constant itself, and skips zx's barrier.
                // NOLINTNEXTLINE(misc-const-correctness)
                unsigned char empty_rlp = zx(0x80);
#if defined(MONAD_ZKVM_ZISK)
                node_id_wire_t const *const first = children;
                for (node_id_wire_t const *c = first + 16; c != first;) {
#else
                node_id_wire_t const *const first = children.data();
                for (node_id_wire_t const *c = first + children.size();
                     c != first;) {
#endif
                    --c;
#if defined(MONAD_ZKVM_ZISK)
                    // The slot is read through c's new value: folded into the
                    // old one's offset, both stay live and every turn ends
                    // copying one into the other.
                    asm("" : "+r"(c));
#endif
                    uint64_t const w = *c;
                    if (w == 0) {
                        // An empty child needs no room test: a span is only
                        // ever made whole, over MAX_NODE_RLP bytes, and a
                        // branch's RLP is 532 at most.
                        static_assert(
                            3 + 16 * HASH_RLP_LEN + 1 <= MAX_NODE_RLP);
                        dest = dest.prepend_unchecked(empty_rlp);
                        continue;
                    }
#if defined(MONAD_ZKVM_ZISK)
                    if constexpr (claims) {
                        // The constructor's claim, before anything of the
                        // child is read: a node start the walk marked, not yet
                        // claimed by another parent (see is_valid_offset).
                        MONAD_ASSERT(w < blob_size && marks[w] != 0);
                        marks[w] = 0;
                        claimed += DIGEST_NODE_LEN;
                    }
#endif
                    if (!digest_at(w)) {
                        dest = child_ref<priming_pass>(NodeId{w}, dest);
#if defined(MONAD_ZKVM_ZISK)
                        if constexpr (priming_pass) {
                            // Where the ref of a child that can become dirty
                            // starts, for patch_rlp: at child index * 8 in the
                            // buffer's head, which a branch's RLP never reaches.
                            // A digest or an empty child never becomes dirty.
                            static_assert(
                                MAX_NODE_RLP - (3 + 16 * HASH_RLP_LEN + 1) >=
                                16 * sizeof(uint64_t));
                            reinterpret_cast<uint64_t *>(
                                dest.base())[c - first] = dest.size();
                        }
#endif
                        continue;
                    }
                    // copy any contiguous digests directly into dest, since a
                    // digest node is already a valid RLP string
                    static_assert(DIGEST == 0x80 + KECCAK256_SIZE);
                    node_id_wire_t const *lo = c;
                    // The slot below extends the run if it holds the offset
                    // one digest below the run's lowest, `below`, counted down
                    // in place, so no value passes from one turn's register to
                    // the next. Not unrolled: gcc's copies of the body would
                    // pass lo and below between them in moves. A slot equal to
                    // `below` lies under w, so it is not an overlay id.
                    // The claims pass has no bound test: its children lie over
                    // the constructor's zero slot, which ends a run -- zero
                    // equals `below` only when `below` is zero, and offset zero
                    // is the magic, which the walk never marks.
                    uint64_t below = w - HASH_RLP_LEN;
#pragma GCC unroll 1
                    while (claims || lo != first) {
                        uint64_t const prev = lo[-1];
                        if (prev != below) {
                            break;
                        }
                        if constexpr (priming_pass) {
                            // The tag alone decides: a null slot reads the
                            // blob's first byte, the magic's 'M' that read_root
                            // asserts, i.e. EMPTY, never DIGEST.
                            if (NodeViewBase{blob + prev}.tag() !=
                                Tag::DIGEST) {
                                break;
                            }
                        }
                        else if (!blob_digest_at(prev)) {
                            break;
                        }
#if defined(MONAD_ZKVM_ZISK)
                        if constexpr (claims) {
                            // Under w, so inside the blob, and the digest after
                            // it in the walk's exact tiling, so a node start:
                            // only its claim is left.
                            MONAD_ASSERT(marks[prev] != 0);
                            marks[prev] = 0;
                        }
#endif
                        below -= HASH_RLP_LEN;
                        --lo;
                    }
#if defined(MONAD_ZKVM_ZISK)
                    if constexpr (claims) {
                        // The run's digests under w, one claim each.
                        claimed += (w - below) - HASH_RLP_LEN;
                    }
#endif
                    // From the run's lowest digest, at below + HASH_RLP_LEN,
                    // to the end of the one at w: `below` has counted the
                    // length already.
                    size_t const digests_length = w - below;

                    unsigned char *const digests =
                        dest.last(digests_length).data();
                    std::memcpy(
                        digests,
                        blob + (below + HASH_RLP_LEN),
                        digests_length);

                    dest = dest.shrink(digests_length);
                    c = lo; // the next turn's decrement steps past the run
                }
#if defined(MONAD_ZKVM_ZISK)
                if constexpr (claims) {
                    claimed_bytes_ += claimed;
                }
#endif
                return wrap(dest);
            },
            [&, encode_path, wrap](ExtView e) -> node_rlp_span {
                // child ref — last element
                dest = child_ref<priming_pass>(e.child(), dest);
                dest = encode_path(dest, e.path(), /*terminating=*/false);
                return wrap(dest);
            },
            [&, encode_path, wrap](AccountLeafView l) -> node_rlp_span {
                // The leaf's value is the account's canonical RLP, which the
                // node no longer holds whole: rebuild it straight into dest's
                // tail — last field first, like everything else here —
                // splicing the storage subtree's own hash in between the
                // stored code_hash and nonce ‖ balance run. Reading the root
                // through hash() is what ties the account to its storage — a
                // leaf can only claim the root its subtree actually hashes to,
                // and NULL_ID resolves to NULL_ROOT, i.e. no storage at all.
                dest = encode_rlp(l.code_hash_rlp(), dest);
                dest = encode_rlp(hash(l.storage()), dest);
                byte_string_view const nonce_balance = l.nonce_balance_rlp();
                std::memcpy(
                    dest.last(nonce_balance.size()).data(),
                    nonce_balance.data(),
                    nonce_balance.size());
                dest = dest.shrink(nonce_balance.size());
                // The value is the first thing a leaf writes, so what stands
                // in the buffer is exactly the account's payload: wrap closes
                // it as the account list.
                dest = wrap(dest);
                // That list is in turn the leaf's value string. Its length is
                // 68..108 of payload plus the 2-byte list header, so the
                // string header is always 0xB7 + 1 followed by one length
                // byte.
                size_t const account_len = dest.rlp_size();
                MONAD_DEBUG_ASSERT(account_len > 55 && account_len <= 0xFF);
                dest.back() = static_cast<unsigned char>(account_len);
                dest = dest.shrink(1);
                dest.back() = zx(0xB8);
                dest = dest.shrink(1);
                dest = encode_path(dest, l.path(), /*terminating=*/true);
                return wrap(dest);
            },
                [&, encode_path, wrap](StorageLeafView l) -> node_rlp_span {
                    // 8-aligned so zeroless_view32's word reads are 16 cells and
                    // not 191.
                    alignas(8) bytes32_t const v = l.value();
                // storage value = rlp(zeroless(slot)), itself wrapped again
                // as the leaf's value string: write the inner rlp(zl) into
                // dest's tail, then prepend the outer string prefix in
                // place.
                auto const val = zeroless_view32(v.bytes);
                size_t const val_len = rlp::string_length(val);
                rlp::encode_string(dest.last(val_len), val);
                dest = dest.shrink(val_len);
                // The outer wrap collapses to no prefix only when it wraps
                // a single byte <=0x7F, i.e. zl itself is one byte <=0x7F.
                if (!(val.size() == 1 && val[0] <= 0x7F)) {
                    dest.back() = zx(0x80 + val_len);
                    dest = dest.shrink(1);
                }
                dest = encode_path(dest, l.path(), /*terminating=*/true);
                return wrap(dest);
            },
            [](DigestView) -> node_rlp_span { std::unreachable(); },
            [](NullView) -> node_rlp_span { std::unreachable(); },
        });
}

namespace
{
    // Narrow `v` to the wire child field and append it little-endian, matching
    // read_node_id.
    void append_node_id(byte_string &b, NodeId const v)
    {
        static_assert(std::endian::native == std::endian::little);
        auto const wire = to_node_id_wire_t(v);
        b.append(reinterpret_cast<unsigned char const *>(&wire), sizeof(wire));
    }

    // Children already narrowed to the wire field: the array is exactly the
    // payload, so it copies in one go rather than word by word. Only
    // put_branch builds children in this form, so it stays local to this TU.
    void append_branch(
        byte_string &out, std::array<node_id_wire_t, 16> const &children)
    {
        static_assert(std::endian::native == std::endian::little);
        out.reserve(out.size() + 1 + 16 * sizeof(node_id_wire_t));
        out.push_back(BRANCH);
        out.append(
            reinterpret_cast<unsigned char const *>(children.data()),
            children.size() * sizeof(node_id_wire_t));
    }

    // Append a path as nodes store it: a 1-byte nibble count then
    // ceil(nlen/2) packed nibbles, left-aligned (nibble 0 in the high
    // nibble of the first byte) — exactly what path_view reads back.
    void append_path(byte_string &b, NibblesView const path)
    {
        unsigned const nlen = path.nibble_size();
        MONAD_ASSERT(nlen <= MAX_PATH_NIBBLES);
        b.push_back(static_cast<unsigned char>(nlen));
        size_t const start = b.size();
        b.resize(start + (nlen + 1) / 2, 0);
        if (nlen == 0) {
            return;
        }
        // The destination is byte-aligned by construction -- nibble 0 goes to
        // the high half of b[start] -- so what follows is a BYTE run, not a
        // nibble run: a straight copy when the source also starts on a byte
        // boundary, one uniform 4-bit shift when it does not. Same shape as
        // compact_encode_raw, and the same reason: paths here run 56-59
        // nibbles, so the nibble loop paid a shift and a read-modify-write 57
        // times over.
        unsigned char *const dst = b.data() + start;
        unsigned char const *const src = path.data();
        bool const odd_start = path.begin_nibble(); // the run starts mid-byte
        unsigned const whole = nlen / 2; // destination bytes a copy can fill
        if (!odd_start) {
            std::memcpy(dst, src, whole);
        }
        else {
            mpt::shift_nibbles_left(dst, src, whole);
        }
        if (nlen % 2) {
            // An odd count leaves one nibble in the high half of the last byte,
            // whose low half has to stay zero -- so that byte cannot come from
            // a byte copy.
            set_nibble(dst, nlen - 1, path.get(nlen - 1));
        }
    }

    unsigned common_prefix_length(NibblesView const a, NibblesView const b)
    {
        return nibble_mismatch(a, b);
    }
}

void append_branch(byte_string &out, std::array<NodeId, 16> const &children)
{
    // Pack child IDs in pairs into an aligned buffer, then append it once.
    // Avoids repeated string updates and unaligned per-child stores.
    static_assert(std::endian::native == std::endian::little);
    static_assert(sizeof(node_id_wire_t) == 4);
    alignas(8) unsigned char buf[16 * sizeof(node_id_wire_t)];
    for (unsigned i = 0; i < 16; i += 2) {
        auto const lo = static_cast<node_id_wire_t>(children[i]);
        auto const hi = static_cast<node_id_wire_t>(children[i + 1]);
        // Ensure both IDs fit in the 32-bit wire format.
        MONAD_ASSERT(static_cast<uint64_t>(children[i]) == lo);
        MONAD_ASSERT(static_cast<uint64_t>(children[i + 1]) == hi);
        uint64_t const w =
            static_cast<uint64_t>(lo) | (static_cast<uint64_t>(hi) << 32);
        __builtin_memcpy(buf + i * sizeof(node_id_wire_t), &w, sizeof(w));
    }
    out.reserve(out.size() + 1 + sizeof(buf));
    out.push_back(BRANCH);
    out.append(buf, sizeof(buf));
}

void append_ext(byte_string &out, NibblesView const path, NodeId const child)
{
    out.push_back(EXT);
    append_node_id(out, child);
    append_path(out, path);
}

void append_storage(
    byte_string &out, NibblesView const path, bytes32_t const &value)
{
    out.push_back(LEAF_STORAGE);
    out.append(value.bytes, 32);
    append_path(out, path);
}

namespace
{
    // Append `n` as an RLP string, straight into `out`.
    // The scan is to_big_compact's: find the top non-zero word by compares.
    void append_unsigned_rlp(byte_string &out, uint256_t const &n)
    {
        size_t w = uint256_t::num_words;
        while (w != 0 && n[w - 1] == 0) {
            --w;
        }
        if (w == 0) {
            out.push_back(zx(0x80)); // RLP of zero is the empty string
            return;
        }
        // top = number of significant bytes in n's highest word
        unsigned const top =
            8u - static_cast<unsigned>(std::countl_zero(n[w - 1]) >> 3);
        // len = total number of significant bytes in n
        size_t const len = (w - 1) * 8 + top;
        alignas(8) unsigned char be[uint256_t::num_bytes];
        for (size_t i = 0; i < w; ++i) {
            uint64_t const b = bswap(n[i]);
            std::memcpy(be + (w - 1 - i) * 8, &b, sizeof(b));
        }
        unsigned char const *const p = be + (w * 8 - len);
        // Nonce and balance never reach 56 bytes, so the long form cannot arise
        // and the header is always one byte.
        if (len == 1 && p[0] <= 0x7f) {
            out.push_back(p[0]);
            return;
        }
        out.push_back(zx(0x80 + len));
        out.append(p, len);
    }

}

void append_acct(
    byte_string &out, NodeId const storage, Account const &acct,
    NibblesView const path)
{
    out.push_back(LEAF_ACCT);
    append_node_id(out, storage);
    // A code hash is always 32 bytes, so its RLP is always the one-byte header
    // 0x80 + 32 and then the bytes -- never the long form, never the
    // single-byte form -- and a 33-byte temporary for a constant header costs
    // an allocation and two copies per account.
    static_assert(sizeof(acct.code_hash) == 32);
    out.push_back(zx(0x80 + 32));
    out.append(acct.code_hash.bytes, sizeof(acct.code_hash.bytes));
    // The length is only known once nonce ‖ balance are encoded, and the
    // appends below may reallocate, so hold slot by index
    size_t const len_index = out.size();
    out.push_back(0);
    append_unsigned_rlp(out, uint256_t{acct.nonce});
    append_unsigned_rlp(out, acct.balance);
    size_t const len = out.size() - len_index - 1;
    MONAD_DEBUG_ASSERT(len >= 2 && len <= MAX_NONCE_BALANCE_RLP_LEN);
    out[len_index] = static_cast<unsigned char>(len);
    append_path(out, path);
}

void append_digest(byte_string &out, bytes32_t const &hash)
{
    out.push_back(zx(DIGEST));
    out.append(hash.bytes, 32);
}

NodeId OffsetTrie::fresh_id()
{
    NodeId const fresh = next_id_;
#if defined(MONAD_ZKVM_ZISK)
    // Every fresh id has a slot in the fresh tables.
    MONAD_ASSERT(static_cast<uint64_t>(fresh) - OVERLAY_BASE < FRESH_HASH_SLOTS);
#endif
    next_id_ = NodeId{static_cast<uint64_t>(next_id_) + 1};
    return fresh;
}

NodeId OffsetTrie::put_node(NodeId const id, byte_string node)
{
#if defined(MONAD_ZKVM_ZISK)
    if (id == NULL_ID) {
        NodeId const fresh = fresh_id();
        fresh_overlay_slots_[static_cast<uint64_t>(fresh) - OVERLAY_BASE] =
            new byte_string(std::move(node));
        return fresh;
    }
    drop_hash(id); // bytes changed; the cached hash is stale
    uint64_t const v = static_cast<uint64_t>(id);
    byte_string *&slot = v < OVERLAY_BASE
                             ? blob_overlay_slots_[v >> 2]
                             : fresh_overlay_slots_[v - OVERLAY_BASE];
    if (slot == nullptr) {
        slot = new byte_string(std::move(node));
    }
    else {
        *slot = std::move(node);
    }
    return id;
#else
    if (id == NULL_ID) {
        NodeId const fresh = fresh_id();
        overlay_filter_mark(fresh); // must precede/accompany every insert
        overlay_[fresh] = std::move(node);
        return fresh;
    }
    drop_hash(id); // bytes changed; the cached hash is stale
    overlay_filter_mark(id);
    overlay_[id] = std::move(node);
    return id;
#endif
}

NodeId OffsetTrie::put_branch(
    NodeId const id, std::array<node_id_wire_t, 16> const &children)
{
    byte_string node;
    append_branch(node, children);
    return put_node(id, std::move(node));
}

NodeId
OffsetTrie::put_ext(NodeId const id, NibblesView const path, NodeId const child)
{
    byte_string node;
    node.reserve(1 + sizeof(node_id_wire_t) + MAX_STORED_PATH_LEN);
    append_ext(node, path, child);
    return put_node(id, std::move(node));
}

NodeId OffsetTrie::put_storage(
    NodeId const id, NibblesView const path, bytes32_t const &value)
{
    byte_string node;
    node.reserve(1 + 32 + MAX_STORED_PATH_LEN);
    append_storage(node, path, value);
    return put_node(id, std::move(node));
}

NodeId OffsetTrie::clone_acct(
    NodeId const id, AccountLeafView const acc, NibblesView const new_path)
{
    // Everything up to the path — tag, storage edge and both field runs — is
    // copied verbatim, so re-pathing neither decodes nor re-encodes it.
    byte_string node{
        acc.bytes(), rlp_end(code_hash_end(child_end(acc.payload())))};
    append_path(node, new_path);
    return put_node(id, std::move(node));
}

NodeId OffsetTrie::put_acct(
    NodeId const id, NibblesView const path, Account const &acct,
    NodeId const storage)
{
    // No storage root to pass: the leaf's hash takes it from `storage` itself.
    byte_string node;
    node.reserve(
        1 + sizeof(node_id_wire_t) + 33 + 1 + MAX_NONCE_BALANCE_RLP_LEN +
        MAX_STORED_PATH_LEN);
    append_acct(node, storage, acct, path);
    return put_node(id, std::move(node));
}

void OffsetTrie::fold_ext_node_path_maybe(
    NodeId const ext_parent, NibblesView const prefix, NodeViewBase const child)
{
    MONAD_ASSERT(ext_parent != NULL_ID);
    MONAD_DEBUG_ASSERT(child.tag() != EMPTY);

    match(
        child,
        Cases{
            // A branch can't absorb a path prefix — caller wraps it in ext.
            [](BranchView) {},
            [&](ExtView e) {
                put_ext(ext_parent, concat(prefix, e.path()), e.child());
            },
            [&](StorageLeafView l) {
                put_storage(ext_parent, concat(prefix, l.path()), l.value());
            },
            [&](AccountLeafView l) {
                clone_acct(ext_parent, l, concat(prefix, l.path()));
            },
            [](DigestView) {
                MONAD_ABORT("incomplete witness: collapse hit a Digest");
            },
            // Callers only fold a surviving child into its parent's path.
            [](NullView) { std::unreachable(); },
        });
}

// The path comes back as a VIEW, not an owning Nibbles. Every path returned
// below is a suffix of `key`, which is the caller's -- in commit() a keccak256
// local that outlives the put_* it hands the path to -- so the copy the owning
// type forced was an allocation and a path copy per upsert for nothing. The
// owning `p` in the ExtView arm stays: that one views the overlay, which the
// put_*s below it move.
std::pair<NodeId, NibblesView>
OffsetTrie::upsert_node(NodeId id, NibblesView key)
{
    using Result = std::pair<NodeId, NibblesView>;
    // A descent to an existing child -- through a branch, or through an
    // extension whose whole path the key starts with -- is the next turn with
    // the child's id and the rest of the key: a call cost a frame a level.
    for (;;) {
        // dirtied along the descent
        [[maybe_unused]] CachedHash *const self = drop_hash(id);
        // Leaf split/overwrite, shared by both leaf types. Only re-emitting the
        // displaced old leaf differs (`reput_old`): a storage leaf keeps its
        // value, an account leaf its fields and storage edge. `reput_old` runs
        // ahead of every other put_* here, which is what lets it still read the
        // displaced leaf's bytes.
        auto const split_leaf = [&](NibblesView const path,
                                    auto const &reput_old) -> Result {
            if (path == key) { // exact match -> overwrite (reuse id + its path)
                return {id, key};
            }
            // old leaf + new key meet at a fresh branch, wrapped in an
            // extension for their shared prefix.
            unsigned const cp = common_prefix_length(path, key);
            MONAD_ASSERT(cp < path.nibble_size() && cp < key.nibble_size());
            std::array<node_id_wire_t, 16> children{};
            children[path.get(cp)] =
                to_node_id_wire_t(reput_old(path.substr(cp + 1)));
            NodeId const leaf = fresh_id();
            children[key.get(cp)] = to_node_id_wire_t(leaf);
            if (cp > 0) {
                NodeId const branch = put_branch(NULL_ID, children);
                put_ext(id, key.substr(0, cp), branch);
            }
            else {
                put_branch(id, children);
            }
            return {leaf, key.substr(cp + 1)};
        };

        std::optional<Result> const done = match(
            get_current(id),
            Cases{
                [&](NullView) -> std::optional<Result> {
                    // Empty slot (or an empty trie's root): a fresh leaf
                    // holding the whole remaining key, which the caller
                    // materialises.
                    return Result{fresh_id(), key};
                },
                [&](StorageLeafView l) -> std::optional<Result> {
                    bytes32_t const v = l.value();
                    return split_leaf(l.path(), [&](NibblesView const np) {
                        return put_storage(NULL_ID, np, v);
                    });
                },
                [&](AccountLeafView l) -> std::optional<Result> {
                    return split_leaf(l.path(), [&, l](NibblesView const np) {
                        return clone_acct(NULL_ID, l, np);
                    });
                },
                [&](ExtView e) -> std::optional<Result> {
                    Nibbles const p{e.path()};
                    NibblesView const path{p};
                    NodeId child = e.child();
                    unsigned const cp = common_prefix_length(path, key);
                    if (cp == path.nibble_size()) { // full prefix -> descend
#if defined(MONAD_ZKVM_ZISK)
                        mark_dirty(self, 0);
#endif
                        key = key.substr(cp);
                        id = child;
                        return std::nullopt;
                    }
                    // diverge mid-extension
                    std::array<node_id_wire_t, 16> children{};
                    if (cp + 1 < path.nibble_size()) {
                        child = put_ext(NULL_ID, path.substr(cp + 1), child);
                    }
                    children[path.get(cp)] = to_node_id_wire_t(child);

                    NodeId const leaf = fresh_id();
                    children[key.get(cp)] = to_node_id_wire_t(leaf);

                    if (cp > 0) {
                        NodeId const branch = put_branch(NULL_ID, children);
                        put_ext(id, key.substr(0, cp), branch);
                    }
                    else {
                        put_branch(id, children);
                    }
                    return Result{leaf, key.substr(cp + 1)};
                },
                [&](BranchView b) -> std::optional<Result> {
                    MONAD_ASSERT(key.nibble_size() > 0); // never ends at branch
                    unsigned const nib = key.get(0);
                    // The rest of the key, in place: nothing below reads the
                    // key before it. Through a copy and back, gcc repacked the
                    // view's parity and end into one register on every level.
                    key.drop_front1();
                    // After drop_front1, as in find_original: read before it,
                    // the child is widened past its branch.
                    NodeId const child = b.child(nib);
                    if (child != NULL_ID) {
#if defined(MONAD_ZKVM_ZISK)
                        mark_dirty(self, nib);
#endif
                        id = child;
                        return std::nullopt;
                    }
                    // A previously-empty slot fills, so the branch is
                    // rewritten and its sixteen children are needed. Read them
                    // before recursing.
                    std::array<node_id_wire_t, 16> children = b.children();
                    auto const result = upsert_node(NULL_ID, key);
                    children[nib] = to_node_id_wire_t(result.first);
                    put_branch(id, children);
                    return result;
                },
                [&](DigestView) -> std::optional<Result> {
                    MONAD_ABORT("incomplete witness: upsert hit a Digest");
                },
            });
        if (done.has_value()) {
            return *done;
        }
    }
}

OffsetTrie::EraseResult
OffsetTrie::erase_node(NodeId const id, NibblesView const key)
{
    return match(
        get_current(id),
        Cases{
            [&](NullView) -> OffsetTrie::EraseResult { // absent
                return OffsetTrie::EraseResult::Unmodified;
            },
            [&](StorageLeafView l) -> OffsetTrie::EraseResult {
                return l.path() == key ? OffsetTrie::EraseResult::Erased
                                       : OffsetTrie::EraseResult::Unmodified;
            },
            [&](AccountLeafView l) -> OffsetTrie::EraseResult {
                return l.path() == key ? OffsetTrie::EraseResult::Erased
                                       : OffsetTrie::EraseResult::Unmodified;
            },
            [&](ExtView e) -> OffsetTrie::EraseResult {
                NodeId const child_id = e.child();
                MONAD_ASSERT(child_id != NULL_ID);
                Nibbles const p{e.path()};
                NibblesView const path{p};
                unsigned const cp = common_prefix_length(path, key);
                if (cp < path.nibble_size()) { // key not under this ext
                    return OffsetTrie::EraseResult::Unmodified;
                }
                auto const erase_child = erase_node(child_id, key.substr(cp));
                if (erase_child ==
                    OffsetTrie::EraseResult::Erased) { // child gone -> ext
                                                       // gone
                    return OffsetTrie::EraseResult::Erased;
                }
                if (erase_child == OffsetTrie::EraseResult::Unmodified) {
                    return OffsetTrie::EraseResult::Unmodified;
                }
                // child survived; fold the ext path into it if it collapsed
                // to a leaf/ext, but keep `id` of the ext node. A branch child
                // leaves the extension's bytes alone and changes its ref.
                [[maybe_unused]] CachedHash *const self = drop_hash(id);
#if defined(MONAD_ZKVM_ZISK)
                mark_dirty(self, 0);
#endif
                NodeViewBase const child = get_current(child_id);
                return match(
                    child,
                    Cases{
                        [](NullView) -> OffsetTrie::EraseResult {
                            MONAD_ABORT("malformed trie: node not found");
                        },
                        [&](auto) {
                            fold_ext_node_path_maybe(id, path, child);
                            return OffsetTrie::EraseResult::Modified;
                        }});
            },
            [&](BranchView b) -> OffsetTrie::EraseResult {
                MONAD_ASSERT(key.nibble_size() > 0);
                unsigned const branch = key.get(0);
                std::array<node_id_wire_t, 16> children = b.children();
                NodeId const child = NodeId{children[branch]};
                if (child == NULL_ID) {
                    return OffsetTrie::EraseResult::Unmodified;
                }
                auto const erase_child = erase_node(child, key.substr(1));
                if (erase_child == OffsetTrie::EraseResult::Unmodified) {
                    return OffsetTrie::EraseResult::Unmodified;
                }
                drop_hash(id);
                if (erase_child == OffsetTrie::EraseResult::Erased) {
                    children[branch] = to_node_id_wire_t(NULL_ID);
                }
                unsigned count = 0;
                unsigned single = 0;
                for (unsigned i = 0; i < 16 && count < 2; ++i) {
                    if (NodeId{children[i]} != NULL_ID) {
                        ++count;
                        single = i;
                    }
                }
                if (count == 0) {
                    return OffsetTrie::EraseResult::Erased;
                }
                if (count == 1) {
                    // collapse: fold the branch nibble into the sole child;
                    // if that child is itself a branch, wrap it in a
                    // one-nibble extension instead.
                    Nibbles const child_path =
                        concat(static_cast<unsigned char>(single));
                    NodeId single_child = NodeId{children[single]};
                    NodeViewBase const child = get_current(single_child);
                    return match(
                        child,
                        Cases{
                            [](NullView) -> OffsetTrie::EraseResult {
                                MONAD_ABORT("malformed trie: node not found");
                            },
                            [&](BranchView) {
                                put_ext(
                                    id, NibblesView{child_path}, single_child);
                                return OffsetTrie::EraseResult::Modified;
                            },
                            [&](auto) {
                                fold_ext_node_path_maybe(
                                    id, NibblesView{child_path}, child);
                                return OffsetTrie::EraseResult::Modified;
                            }});
                }
                else {
                    put_branch(id, children); // >=2 survivors: stays
                    return OffsetTrie::EraseResult::Modified;
                }
            },
            [&](DigestView) -> OffsetTrie::EraseResult {
                MONAD_ABORT("incomplete witness: erase hit a Digest");
            },
        });
}

MONAD_MPT_NAMESPACE_END
