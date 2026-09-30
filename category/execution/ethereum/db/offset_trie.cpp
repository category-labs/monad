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
#include <span>
#include <utility>
#include <vector>

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
    // This unsigned subtraction may wrap for a short blob. read_root then
    // rejects it before construction completes or any lookup can run.
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
    // One byte per blob offset avoids bit extraction and read-modify-write
    // updates. This uses more memory than a bitmap.
#if defined(MONAD_ZKVM_ZISK)
    // Fresh ZisK bump allocations are never reused and read as zero before
    // their first write. No explicit clear or deallocation is needed here.
    std::span<unsigned char> const node_marks{
        static_cast<unsigned char *>(::operator new(blob_.size())),
        blob_.size()};
    claim_marks_ = node_marks.data();
#else
    std::vector<unsigned char> node_marks(blob_.size(), 0);
#endif
    // Follow the current node with a mark pointer. Digest nodes can advance
    // it directly without recomputing their offset from the blob base.
    unsigned char *current_node_mark = node_marks.data() + node_offset;

    // Reserve before priming to avoid rehashing. The measured corpus has
    // about one cached hash per 430 blob bytes; /256 leaves spare capacity.
#if defined(MONAD_ZKVM_ZISK)
    // Allocate direct slot tables and an initial pool of hash entries.
    blob_node_cache_ = static_cast<NodeCacheEntry **>(
        ::operator new((blob_.size() / 4 + 1) * sizeof(NodeCacheEntry *)));
    new_node_cache_ = static_cast<NodeCacheEntry **>(
        ::operator new(FRESH_HASH_SLOTS * sizeof(NodeCacheEntry *)));
    refill_hash_pool(blob_.size() / 256 + 1);
#else
    hashes_.reserve(blob_.size() / 256);
#endif
#if defined(MONAD_ZKVM_ZISK)
    modified_blob_nodes_ = static_cast<byte_string **>(
        ::operator new((blob_.size() / 4 + 1) * sizeof(byte_string *)));
    new_nodes_ = static_cast<byte_string **>(
        ::operator new(FRESH_HASH_SLOTS * sizeof(byte_string *)));
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
    // remains, without scanning the marks again.
    size_t unclaimed_bytes = static_cast<size_t>(region_end - node.bytes());

#if !defined(MONAD_ZKVM_ZISK)
    // Reuse a valid entry as Keccak output, then copy it into the cache.
    // This avoids reinitializing the entry for every node.
    NodeCacheEntry hash_entry{};
    hash_entry.hash_valid = true;
#endif

    // Cache the size so possible aliasing with mark stores does not
    // force GCC to reload it for each child.
    size_t const blob_size = blob_.size();
    auto const claim_child = [&](NodeId child) {
        if (child == NULL_ID) {
            return;
        }
        uint64_t child_offset = static_cast<uint64_t>(child);
        MONAD_ASSERT(child_offset < blob_size && node_marks[child_offset] != 0);
        node_marks[child_offset] = 0;
        unclaimed_bytes -= DIGEST_NODE_LEN;
    };
    unsigned char rlp_buf[MAX_NODE_RLP];

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
            *current_node_mark = 1;
            current_node_mark += DIGEST_NODE_LEN;
            node = NodeViewBase{node.bytes() + DIGEST_NODE_LEN};
            continue;
        }
        // Only nondigest nodes need their offset for hashing and marking.
        node_offset = static_cast<uint64_t>(node.bytes() - base);

        // checked_end asserts that the current node does not reach past the end
        // of the region
        auto next_offset =
            static_cast<uint64_t>(node.checked_end(region_end) - base);

        match(
            node,
            Cases{
                [&](BranchView b) {
                    // ZisK reuses an aligned copy during encoding. The host
                    // validates all eight pairs here, with two child IDs per
                    // load.
                    static_assert(std::endian::native == std::endian::little);
                    static_assert(
                        sizeof(uint64_t) == 2 * sizeof(node_id_wire_t));
#if defined(MONAD_ZKVM_ZISK)
                    // Copy once; the priming encode validates each child before
                    // use.
                    std::memcpy(
                        primed_slots_ + PRIMED_CHILDREN_OFFSET,
                        b.payload(),
                        BRANCH_CHILD_COUNT * sizeof(node_id_wire_t));
#else
                    unsigned char const *const child_payload = b.payload();
                    uint64_t child_pair;
    #pragma GCC unroll 8
                    for (unsigned pair_index = 0; pair_index < 8;
                         ++pair_index) {
                        std::memcpy(
                            &child_pair,
                            child_payload + pair_index * sizeof(child_pair),
                            sizeof(child_pair));
                        claim_child(
                            NodeId{static_cast<node_id_wire_t>(child_pair)});
                        claim_child(NodeId{
                            static_cast<node_id_wire_t>(child_pair >> 32)});
                    }
#endif
                },
                [&](ExtView e) { claim_child(e.child()); },
                [&](AccountLeafView a) { claim_child(a.storage()); },
                [](auto) {}});

        match(
            node,
            Cases{
                [](NullView) {},
                [](DigestView) {},
                [&](auto) {
#if defined(MONAD_ZKVM_ZISK)
                    node_rlp_span const rem =
                        node.tag() == BRANCH
                            ? encode_rlp<true, true>(
                                  node,
                                  node_rlp_span{rlp_buf},
                                  primed_slots_ + PRIMED_CHILDREN_OFFSET)
                            : encode_rlp<true>(
                                  node, node_rlp_span{rlp_buf}); // priming pass
#else
                    node_rlp_span const rem = encode_rlp<true>(
                        node, node_rlp_span{rlp_buf}); // priming pass
#endif
                    // Only hash-referenced nodes (canonical RLP >= 32 B)
                    // are cached; smaller nodes are inlined by their
                    // parent, so caching their hash would make child_ref
                    // emit a 32-byte ref where the trie inlines it.
                    if (rem.rlp_size() >= 32) {
#if defined(MONAD_ZKVM_ZISK)
                        // The sweep reaches each node once, so its slot is
                        // empty: the digest goes straight into a new entry.
                        NodeCacheEntry *const cached = new_hash_entry();
                        monad_keccak256(
                            rem.rlp_data(), rem.rlp_size(), cached->hash.bytes);
                        blob_node_cache_[node_offset >> 2] = cached;
#else
                        monad_keccak256(
                            rem.rlp_data(), rem.rlp_size(), hash_entry.hash.bytes);
                        hashes_.insert_or_assign(NodeId{node_offset}, hash_entry);
#endif
                    }
                }});

        node_marks[node_offset] = 1;
        unclaimed_bytes =
            unclaimed_bytes + DIGEST_NODE_LEN - (next_offset - node_offset);
        node = NodeViewBase{base + next_offset};
        current_node_mark = node_marks.data() + next_offset;
    }
    MONAD_ASSERT(node.bytes() == region_end); // nodes tile exactly
    claim_child(root);
#if defined(MONAD_ZKVM_ZISK)
    unclaimed_bytes -= claimed_bytes_;
    claim_marks_ = nullptr;
#endif

    // Any remaining count indicates a node unreachable from root.
    MONAD_ASSERT(unclaimed_bytes == 0);
}

#if defined(MONAD_ZKVM_ZISK)
namespace
{
    // Compare nibble_count nibbles from byte boundaries. Ignore the last low
    // nibble for odd lengths: it is padding, not authenticated by the trie
    // hash.
    [[gnu::always_inline]] inline bool aligned_nibbles_equal(
        unsigned char const *const a, unsigned char const *const b,
        unsigned const nibble_count)
    {
        // Two nibbles form one complete byte.
        size_t const whole_bytes = nibble_count / 2;
        // If n is odd, compare the remaining high nibble separately.
        // XOR finds differing bits; 0xf0 keeps only the high half.
        if ((nibble_count & 1) != 0 &&
            ((a[whole_bytes] ^ b[whole_bytes]) & 0xf0) != 0) {
            return false;
        }
        // Any remaining high nibble was checked above.
        if (whole_bytes == 0) {
            return true;
        }
        uint64_t difference;
        // CSR 0x814 compares bytes; the following add encodes the second
        // pointer and the register holding the byte count.
        // The "m" operands tell the compiler that both buffers are read.
        asm(".option push\n\t"
            ".option arch, +zicsr\n\t"
            "csrrs %0, 0x814, %1\n\t"
            "add x0, %2, %3\n\t"
            ".option pop"
            : "=&r"(difference)
            : "r"(a),
              "r"(b),
              "r"(whole_bytes),
              "m"(*reinterpret_cast<
                  unsigned char const(*)[MAX_PATH_NIBBLES / 2]>(a)),
              "m"(*reinterpret_cast<
                  unsigned char const(*)[MAX_PATH_NIBBLES / 2]>(b)));
        // DMA returns zero when all compared bytes match.
        return difference == 0;
    }

    // Compare the leaf path with the remaining key. If the key starts in
    // a low nibble, shift a copy of the full key to allow byte comparison.
    [[gnu::always_inline]] inline bool leaf_path_equals(
        NibblesView const path, NibblesView const key,
        unsigned char const *const whole_key)
    {
        unsigned const nibble_count = path.nibble_size();
        if (nibble_count != key.nibble_size()) {
            return false;
        }
        // An unaligned stored path still needs the general comparison.
        if (path.begin_nibble()) {
            return path == key;
        }
        // Both views already start on a byte boundary.
        if (!key.begin_nibble()) {
            return aligned_nibbles_equal(path.data(), key.data(), nibble_count);
        }
        // Only a lookup starting with a full 32-byte key can use the shift.
        if (whole_key == nullptr) {
            return path == key;
        }
        // Load the full key as four big-endian words.
        uint64_t key_words[4];
    #pragma GCC unroll 1
        for (size_t i = 0; i < 4; ++i) {
            __builtin_memcpy(
                &key_words[i], whole_key + 8 * i, sizeof(key_words[i]));
            key_words[i] = __builtin_bswap64(key_words[i]);
        }
        // Shift left by one nibble, carrying between words, then restore
        // byte order. For example, AB CD EF becomes BC DE F0.
        alignas(8) uint64_t shifted_key[4];
        shifted_key[0] =
            __builtin_bswap64(key_words[0] << 4 | key_words[1] >> 60);
        shifted_key[1] =
            __builtin_bswap64(key_words[1] << 4 | key_words[2] >> 60);
        shifted_key[2] =
            __builtin_bswap64(key_words[2] << 4 | key_words[3] >> 60);
        shifted_key[3] = __builtin_bswap64(key_words[3] << 4);
        // The remaining key starts at nibble 64 - nibble_count in the original
        // key, or 63 - nibble_count after the shift. Divide by two to get its
        // byte offset.
        return aligned_nibbles_equal(
            path.data(),
            reinterpret_cast<unsigned char const *>(shifted_key) +
                (MAX_PATH_NIBBLES - 1 - nibble_count) / 2,
            nibble_count);
    }
}
#endif

NodeViewBase OffsetTrie::find_original(NodeId id, NibblesView key) const
{
#if defined(MONAD_ZKVM_ZISK)
    // Keep the full key for realigning a leaf comparison at an odd depth.
    // During traversal, key remains a suffix of this original input.
    unsigned char const *const whole_key =
        key.nibble_size() == MAX_PATH_NIBBLES && !key.begin_nibble()
            ? key.data()
            : nullptr;
#endif
    NodeViewBase found = empty();
    // Validate the entry ID; an overlay ID is not a valid original root.
    // Descendant IDs were already validated by the blob constructor.
    NodeViewBase node = get_original(id);
#if defined(MONAD_ZKVM_ZISK)
    // Walk consecutive branches using both nibbles of each key byte.
    // Update the key view once, then let the general loop handle other nodes.
    if (whole_key != nullptr) {
        unsigned char const *key_cursor = whole_key;
        // Set if we stop after consuming only the current byte's high nibble.
        unsigned consumed_high_nibble = 0;
        while (id != NULL_ID) {
            if (node.tag() != BRANCH) {
                break;
            }
            if (key_cursor ==
                whole_key + MAX_PATH_NIBBLES / 2) { // no value at a branch
                return found;
            }
            unsigned const key_byte = *key_cursor;
            // The high nibble selects the first child.
            id = BranchView{node}.child(key_byte >> 4);
            if (id == NULL_ID) {
                return found;
            }
            node = original_child(id);
            if (node.tag() != BRANCH) {
                consumed_high_nibble = 1;
                break;
            }
            // If that child is also a branch, use the same byte's low nibble.
            id = BranchView{node}.child(key_byte & 0xf);
            node = original_child(id);
            ++key_cursor;
        }
        // Skip two nibbles per consumed byte, plus the high nibble if needed.
        key = NibblesView{
            2 * static_cast<unsigned>(key_cursor - whole_key) +
                consumed_high_nibble,
            MAX_PATH_NIBBLES,
            whole_key};
    }
#endif
    while (id != NULL_ID) {
        // Test the common branch case before the general tag dispatch.
        if (MONAD_LIKELY(node.tag() == BRANCH)) {
            if (key.nibble_size() == 0) { // no value at a branch
                break;
            }
            id = BranchView{node}.child(key.get(0));
            key = key.substr(1);
            node = original_child(id);
            continue;
        }
        id = match(
            node, Cases {
                [](BranchView) -> NodeId { std::unreachable(); },
                    [&](ExtView e) -> NodeId {
                        NibblesView const extension_path = e.path();
                        if (!key.starts_with(extension_path)) {
                            return NULL_ID;
                        }
                        key = key.substr(extension_path.nibble_size());
                        return e.child();
                    },
                    [&](AccountLeafView l) -> NodeId {
#if defined(MONAD_ZKVM_ZISK)
                        if (leaf_path_equals(l.path(), key, whole_key)) {
#else
                    if (l.path() == key) {
#endif
                            found = l;
                        }
                        return NULL_ID;
                    },
                    [&](StorageLeafView l) -> NodeId {
#if defined(MONAD_ZKVM_ZISK)
                        if (leaf_path_equals(l.path(), key, whole_key)) {
#else
                    if (l.path() == key) {
#endif
                            found = l;
                        }
                        return NULL_ID;
                    },
                    [](DigestView) -> NodeId {
                        MONAD_ABORT("incomplete witness: lookup hit a Digest");
                    },
                    [](NullView) -> NodeId {
                        // The loop excludes the NULL_ID header. Any other null
                        // tag indicates a malformed node.
                        MONAD_ABORT("malformed trie: node not found");
                    },
            });
        node = original_child(id);
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

                unsigned char buf[MAX_NODE_RLP];
                node_rlp_span const rem = encode_rlp(node, node_rlp_span{buf});
                MONAD_ASSERT(rem.rlp_size() >= 32);
                bytes32_t h;
                // RLP occupies the tail: [rem.end(), buf_end).
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
    // Keep previous chunks alive so existing slot pointers remain valid.
    next_cache_entry_ = static_cast<NodeCacheEntry *>(
        ::operator new(entries * sizeof(NodeCacheEntry)));
    cache_entries_end_ = next_cache_entry_ + entries;
}
#endif

template <bool priming_pass>
OffsetTrie::node_rlp_span OffsetTrie::child_ref_compute(
    NodeId const id, NodeViewBase const node, OffsetTrie::node_rlp_span dest)
{
    unsigned char buf[MAX_NODE_RLP];
    node_rlp_span const rem =
        encode_rlp<priming_pass>(node, node_rlp_span{buf});
    unsigned char const *const child_rlp = rem.rlp_data();
    size_t const child_rlp_len = rem.rlp_size();
    if (child_rlp_len < 32) {
        std::memcpy(dest.last(child_rlp_len).data(), child_rlp, child_rlp_len);
        return dest.shrink(child_rlp_len);
    }
    // Priming caches hash-referenced children before their parents. A miss
    // here indicates an invalid witness, not a reason to recurse.
    if constexpr (priming_pass) {
        MONAD_ABORT("offset trie: unprimed hash-referenced node (bad offset)");
    }
    bytes32_t digest;
    monad_keccak256(child_rlp, child_rlp_len, digest.bytes);
    store_hash(id, digest);
    return encode_rlp(digest, dest);
}

namespace
{
    // Like rlp::zeroless_view for a 32-byte big-endian value, but skips
    // leading zeros eight bytes at a time. Reads the aligned stack copy
    // because unaligned word reads from the blob are more expensive on ZisK.
    [[gnu::always_inline]] inline byte_string_view
    zeroless_view32(unsigned char const *const bytes)
    {
        for (unsigned byte_offset = 0; byte_offset < 32; byte_offset += 8) {
            uint64_t const word = bits::load64(bytes + byte_offset);
            if (word == 0) {
                continue;
            }
            // Byte-swap the loaded word to count zeros in big-endian byte
            // order.
#if defined(__riscv_zbb) || defined(__x86_64__) || defined(__aarch64__)
            unsigned const leading_zero_bytes =
                static_cast<unsigned>(std::countl_zero(std::byteswap(word))) /
                8;
#else
            unsigned const leading_zero_bytes =
                static_cast<unsigned>(bits::clz64(bits::bswap64(word))) / 8;
#endif
            return {
                bytes + byte_offset + leading_zero_bytes,
                32 - byte_offset - leading_zero_bytes};
        }
        return {bytes + 32, 0};
    }
}

template <bool priming_pass, bool claim_children>
OffsetTrie::node_rlp_span OffsetTrie::encode_rlp(
    NodeViewBase const node, OffsetTrie::node_rlp_span dest,
    [[maybe_unused]] node_id_wire_t const *const supplied_children)
{
    MONAD_DEBUG_ASSERT(node.tag() != EMPTY && node.tag() != DIGEST);
    if constexpr (claim_children) {
        // The constructor only enables claims for branches. Let the compiler
        // remove the other node cases and their stack buffers.
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
            d.back() = static_cast<unsigned char>(0x80 + path_len);
            d = d.shrink(1);
        }
        return d;
    };
    // Prepend the list prefix directly; node payloads need at most three bytes.
    auto const wrap = [](OffsetTrie::node_rlp_span const payload) {
        size_t const payload_len = payload.rlp_size();
        if (payload_len <= 55) {
            payload.back() = static_cast<unsigned char>(0xC0 + payload_len);
            return payload.shrink(1);
        }
        if (payload_len <= 0xFF) {
            auto const header = payload.last(2);
            header[0] = static_cast<unsigned char>(0xF8);
            header[1] = static_cast<unsigned char>(payload_len);
            return payload.shrink(2);
        }
        // Ensure the payload length fits in the two-byte field below.
        MONAD_ASSERT(payload_len <= 0xFFFF);
        auto const header = payload.last(3);
        header[0] = static_cast<unsigned char>(0xF9);
        header[1] = static_cast<unsigned char>(payload_len >> 8);
        header[2] = static_cast<unsigned char>(payload_len & 0xFF);
        return payload.shrink(3);
    };
    return match(
        node, Cases {
            [&, wrap](BranchView b) -> node_rlp_span {
                dest.back() = 0x80; // empty branch value — last list element
                dest = dest.shrink(1);
#if defined(MONAD_ZKVM_ZISK)
                alignas(8) node_id_wire_t local_children[16];
                node_id_wire_t const *children = supplied_children;
                if (children == nullptr) {
                    std::memcpy(
                        local_children, b.payload(), sizeof(local_children));
                    children = local_children;
                }
#else
                std::array<node_id_wire_t, 16> const children = b.children();
#endif

                // A digest is pre-state only, put_node never shadows a digest
                // id and its original bytes are still its current bytes which
                // is why we can memcpy from the blob_ directly below.
                //
                // Widen wire IDs once to use native 64-bit arithmetic.
                //
                // Keep the blob address across byte stores, which may alias
                // blob_ and otherwise force the compiler to reload it.
                unsigned char const *const blob_data = blob_.data();
                auto const blob_digest_at = [&](uint64_t const w) {
                    if constexpr (priming_pass) {
                        // Children are validated before this read, either by
                        // the constructor or by this encode's claim step.
                        // Inlined children's references were checked earlier.
                        return w != 0 &&
                               NodeViewBase{blob_data + w}.tag() == Tag::DIGEST;
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
                [[maybe_unused]] unsigned char *const unclaimed_node_marks =
                    claim_marks_;
                [[maybe_unused]] size_t const blob_size = blob_.size();
                [[maybe_unused]] size_t claimed_node_bytes = 0;
                static_assert(DIGEST_NODE_LEN == HASH_RLP_LEN);
#endif
            // Walk backwards by pointer to avoid repeated index scaling.
            // Test before decrementing to stay within the array and avoid
            // GCC copying the pointer's old value for the comparison.
#if defined(MONAD_ZKVM_ZISK)
                node_id_wire_t const *const children_begin = children;
                for (node_id_wire_t const *child_cursor = children_begin + 16;
                     child_cursor != children_begin;) {
#else
                node_id_wire_t const *const children_begin = children.data();
                for (node_id_wire_t const *child_cursor = children_begin + children.size();
                     child_cursor != children_begin;) {
#endif
                    --child_cursor;
#if defined(MONAD_ZKVM_ZISK)
                    // Make the load use the decremented pointer, avoiding an
                    // old/new pointer register copy on each iteration.
                    asm("" : "+r"(child_cursor));
#endif
                    uint64_t const child_offset = *child_cursor;
#if defined(MONAD_ZKVM_ZISK)
                    if constexpr (claim_children) {
                        // Before reading the child, require a previously seen
                        // node that no other parent has claimed.
                        if (child_offset != 0) {
                            MONAD_ASSERT(
                                child_offset < blob_size &&
                                unclaimed_node_marks[child_offset] != 0);
                            unclaimed_node_marks[child_offset] = 0;
                            claimed_node_bytes += DIGEST_NODE_LEN;
                        }
                    }
#endif
                    if (!digest_at(child_offset)) {
                        dest =
                            child_ref<priming_pass>(NodeId{child_offset}, dest);
                        continue;
                    }
                    // copy any contiguous digests directly into dest, since a
                    // digest node is already a valid RLP string
                    static_assert(DIGEST == 0x80 + KECCAK256_SIZE);
                    node_id_wire_t const *run_begin = child_cursor;
                    // Expected offset of the preceding digest. The run starts
                    // at preceding_offset + HASH_RLP_LEN when the loop ends.
                    // A matching preceding offset cannot be an overlay ID.
                    // Disable unrolling to avoid extra GCC register moves.
                    // During claims, a zero sentinel before the children ends
                    // the run without a pointer-bound test. If the offset is
                    // zero, the blob's magic byte is not a digest, so it still
                    // stops.
                    uint64_t preceding_offset = child_offset - HASH_RLP_LEN;
#pragma GCC unroll 1
                    while (claim_children || run_begin != children_begin) {
                        uint64_t const previous_child = run_begin[-1];
                        if (previous_child != preceding_offset) {
                            break;
                        }
                        if constexpr (priming_pass) {
                            // Offset zero reads the validated header's EMPTY
                            // tag, never DIGEST, so no separate null check is
                            // needed.
                            if (NodeViewBase{blob_data + previous_child}
                                    .tag() != Tag::DIGEST) {
                                break;
                            }
                        }
                        else if (!blob_digest_at(previous_child)) {
                            break;
                        }
#if defined(MONAD_ZKVM_ZISK)
                        if constexpr (claim_children) {
                            // The matching predecessor lies below a validated
                            // digest offset. Require that no other parent
                            // claimed it.
                            MONAD_ASSERT(
                                unclaimed_node_marks[previous_child] != 0);
                            unclaimed_node_marks[previous_child] = 0;
                        }
#endif
                        preceding_offset -= HASH_RLP_LEN;
                        --run_begin;
                    }
#if defined(MONAD_ZKVM_ZISK)
                    // Make the copy use the final offset, avoiding an extra
                    // old/new offset register copy in the digest loop.
                    asm("" : "+r"(preceding_offset));
#endif
                    // preceding_offset is one digest before the run;
                    // child_offset is its last.
                    // NOLINTNEXTLINE(misc-const-correctness)
                    size_t digests_length = child_offset - preceding_offset;
#if defined(MONAD_ZKVM_ZISK)
                    // Keep the computed run length in a register for the copy
                    // and cursor.
                    asm("" : "+r"(digests_length));
                    if constexpr (claim_children) {
                        // Count the rest of the run; its last digest was
                        // counted above.
                        claimed_node_bytes += digests_length - HASH_RLP_LEN;
                    }
#endif

                    // A complete branch needs at most 532 bytes, within
                    // MAX_NODE_RLP, so this copy needs no extra room check.
                    dest = dest.prepend_unchecked(
                        blob_data + (preceding_offset + HASH_RLP_LEN),
                        digests_length);
                    // The next decrement skips the copied run.
                    child_cursor = run_begin;
                }
#if defined(MONAD_ZKVM_ZISK)
                if constexpr (claim_children) {
                    claimed_bytes_ += claimed_node_bytes;
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
                    // The leaf's value is the account's canonical RLP, which
                    // the node no longer holds whole: rebuild it straight into
                    // dest's tail — last field first, like everything else here
                    // — splicing the storage subtree's own hash in between the
                    // stored code_hash and nonce ‖ balance run. Reading the
                    // root through hash() is what ties the account to its
                    // storage — a leaf can only claim the root its subtree
                    // actually hashes to, and NULL_ID resolves to NULL_ROOT,
                    // i.e. no storage at all.
                    dest = encode_rlp(l.code_hash_rlp(), dest);
                    dest = encode_rlp(hash(l.storage()), dest);
                    byte_string_view const nonce_balance =
                        l.nonce_balance_rlp();
                    std::memcpy(
                        dest.last(nonce_balance.size()).data(),
                        nonce_balance.data(),
                        nonce_balance.size());
                    dest = dest.shrink(nonce_balance.size());
                    // The value is the first thing a leaf writes, so what
                    // stands in the buffer is exactly the account's payload:
                    // wrap closes it as the account list.
                    dest = wrap(dest);
                    // That list is in turn the leaf's value string. Its length
                    // is 68..108 of payload plus the 2-byte list header, so the
                    // string header is always 0xB7 + 1 followed by one length
                    // byte.
                    size_t const account_len = dest.rlp_size();
                    MONAD_DEBUG_ASSERT(account_len > 55 && account_len <= 0xFF);
                    dest.back() = static_cast<unsigned char>(account_len);
                    dest = dest.shrink(1);
                    dest.back() = 0xB8;
                    dest = dest.shrink(1);
                    dest = encode_path(dest, l.path(), /*terminating=*/true);
                    return wrap(dest);
                },
                [&, encode_path, wrap](StorageLeafView l) -> node_rlp_span {
                    // 8-aligned so zeroless_view32's word reads are 16 cells
                    // and not 191.
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
                        dest.back() =
                            static_cast<unsigned char>(0x80 + val_len);
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
    void append_path(byte_string &buffer, NibblesView const path)
    {
        unsigned const nibble_count = path.nibble_size();
        MONAD_ASSERT(nibble_count <= MAX_PATH_NIBBLES);
        buffer.push_back(static_cast<unsigned char>(nibble_count));
        if (nibble_count == 0) {
            return;
        }
        size_t const output_offset = buffer.size();
        buffer.resize(output_offset + (nibble_count + 1) / 2, 0);
        // The output starts at a byte boundary. Copy whole input bytes,
        // or shift by four bits when the path starts in a low nibble.
        unsigned char *const output = buffer.data() + output_offset;
        unsigned char const *const source = path.data();
        bool const odd_start = path.begin_nibble(); // the run starts mid-byte
        unsigned const whole_bytes = nibble_count / 2;
        if (!odd_start) {
            std::memcpy(output, source, whole_bytes);
        }
        else {
            mpt::shift_nibbles_left(output, source, whole_bytes);
        }
        if (nibble_count % 2) {
            // Write the final high nibble; keep the low padding nibble zero.
            set_nibble(output, nibble_count - 1, path.get(nibble_count - 1));
        }
    }
}

void append_branch(byte_string &out, std::array<NodeId, 16> const &children)
{
    out.reserve(out.size() + 1 + 16 * sizeof(node_id_wire_t));
    out.push_back(BRANCH);
    for (NodeId const c : children) {
        append_node_id(out, c);
    }
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
    // Append the integer directly, without allocating a temporary RLP string.
    void append_unsigned_rlp(byte_string &out, uint256_t const &value)
    {
        size_t significant_words = uint256_t::num_words;
        while (significant_words != 0 && value[significant_words - 1] == 0) {
            --significant_words;
        }
        if (significant_words == 0) {
            out.push_back(static_cast<unsigned char>(
                0x80)); // RLP of zero is the empty string
            return;
        }
        // Count significant bytes in the highest nonzero word.
        unsigned const top_word_bytes =
            8u - static_cast<unsigned>(
                     std::countl_zero(value[significant_words - 1]) >> 3);
        // Include all lower words.
        size_t const byte_count = (significant_words - 1) * 8 + top_word_bytes;
        alignas(8) unsigned char big_endian[uint256_t::num_bytes];
        for (size_t i = 0; i < significant_words; ++i) {
            uint64_t const big_endian_word = bswap(value[i]);
            std::memcpy(
                big_endian + (significant_words - 1 - i) * 8,
                &big_endian_word,
                sizeof(big_endian_word));
        }
        unsigned char const *const significant_bytes =
            big_endian + (significant_words * 8 - byte_count);
        // Values fit in 32 bytes: use either the single-byte form or a short
        // string with a one-byte prefix.
        if (byte_count == 1 && significant_bytes[0] <= 0x7f) {
            out.push_back(significant_bytes[0]);
            return;
        }
        out.push_back(static_cast<unsigned char>(0x80 + byte_count));
        out.append(significant_bytes, byte_count);
    }

}

void append_acct(
    byte_string &out, NodeId const storage, Account const &acct,
    NibblesView const path)
{
    out.push_back(LEAF_ACCT);
    append_node_id(out, storage);
    out.append(rlp::encode_bytes32(acct.code_hash));
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
    out.push_back(DIGEST);
    out.append(hash.bytes, 32);
}

NodeId OffsetTrie::fresh_id()
{
    NodeId const fresh = next_id_;
#if defined(MONAD_ZKVM_ZISK)
    // Every fresh id has a slot in the fresh tables.
    MONAD_ASSERT(
        static_cast<uint64_t>(fresh) - OVERLAY_BASE < FRESH_HASH_SLOTS);
#endif
    next_id_ = NodeId{static_cast<uint64_t>(next_id_) + 1};
    return fresh;
}

NodeId OffsetTrie::put_node(NodeId const id, byte_string node)
{
#if defined(MONAD_ZKVM_ZISK)
    if (id == NULL_ID) {
        NodeId const fresh = fresh_id();
        new_nodes_[static_cast<uint64_t>(fresh) - OVERLAY_BASE] =
            new byte_string(std::move(node));
        return fresh;
    }
    drop_hash(id); // bytes changed; the cached hash is stale
    uint64_t const node_id = static_cast<uint64_t>(id);
    byte_string *&slot = node_id < OVERLAY_BASE
                             ? modified_blob_nodes_[node_id >> 2]
                             : new_nodes_[node_id - OVERLAY_BASE];
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
        overlay_[fresh] = std::move(node);
        return fresh;
    }
    drop_hash(id); // bytes changed; the cached hash is stale
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
    append_ext(node, path, child);
    return put_node(id, std::move(node));
}

NodeId OffsetTrie::put_storage(
    NodeId const id, NibblesView const path, bytes32_t const &value)
{
    byte_string node;
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

// Returned paths borrow a suffix of the caller's key, which must outlive them.
// The extension path remains an owning copy: writes may replace its storage.
std::pair<NodeId, NibblesView>
OffsetTrie::upsert_node(NodeId const id, NibblesView const key)
{
#if defined(MONAD_ZKVM_ZISK)
    // Keep the full key so leaf_path_equals can realign an odd-depth suffix.
    unsigned char const *const whole_key =
        key.nibble_size() == MAX_PATH_NIBBLES && !key.begin_nibble()
            ? key.data()
            : nullptr;
#endif
    drop_hash(id); // dirtied along the descent
    // Leaf split/overwrite, shared by both leaf types. Only re-emitting the
    // displaced old leaf differs (`reput_old`): a storage leaf keeps its
    // value, an account leaf its fields and storage edge. `reput_old` runs
    // ahead of every other put_* here, which is what lets it still read the
    // displaced leaf's bytes.
    auto const split_leaf =
        [&](NibblesView const path,
            auto const &reput_old) -> std::pair<NodeId, NibblesView> {
    // exact match -> overwrite (reuse id + its path)
#if defined(MONAD_ZKVM_ZISK)
        if (leaf_path_equals(path, key, whole_key)) {
#else
        if (path == key) {
#endif
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

    return match(
        get_current(id),
        Cases{
            [&](NullView) -> std::pair<NodeId, NibblesView> {
                // Empty slot (or an empty trie's root): a fresh leaf
                // holding the whole remaining key, which the caller
                // materialises.
                return {fresh_id(), key};
            },
            [&](StorageLeafView l) -> std::pair<NodeId, NibblesView> {
                bytes32_t const v = l.value();
                return split_leaf(
                    l.path(), [&](NibblesView const remaining_path) {
                        return put_storage(NULL_ID, remaining_path, v);
                    });
            },
            [&](AccountLeafView l) -> std::pair<NodeId, NibblesView> {
                return split_leaf(
                    l.path(), [&, l](NibblesView const remaining_path) {
                        return clone_acct(NULL_ID, l, remaining_path);
                    });
            },
            [&](ExtView e) -> std::pair<NodeId, NibblesView> {
                Nibbles const owned_path{e.path()};
                NibblesView const path{owned_path};
                NodeId child = e.child();
                unsigned const cp = common_prefix_length(path, key);
                if (cp == path.nibble_size()) { // full prefix -> descend
                    return upsert_node(child, key.substr(cp));
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
                return {leaf, key.substr(cp + 1)};
            },
            [&](BranchView b) -> std::pair<NodeId, NibblesView> {
                MONAD_ASSERT(key.nibble_size() > 0); // never ends at branch
                unsigned const nib = key.get(0);
                std::array<node_id_wire_t, 16> children = b.children();
                NodeId const child = NodeId{children[nib]};
                // Recurse into the slot: a NULL_ID child lets upsert_node
                // allocate the leaf; an existing child keeps its stable id.
                // Only rewrite the branch when a previously-empty slot
                // fills.
                auto const result = upsert_node(child, key.substr(1));
                if (child == NULL_ID) {
                    children[nib] = to_node_id_wire_t(result.first);
                    put_branch(id, children);
                }
                return result;
            },
            [&](DigestView) -> std::pair<NodeId, NibblesView> {
                MONAD_ABORT("incomplete witness: upsert hit a Digest");
            },
        });
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
                // to a leaf/ext, but keep `id` of the ext node
                drop_hash(id);
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
