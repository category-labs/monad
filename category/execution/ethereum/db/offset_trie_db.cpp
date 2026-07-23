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

#include <category/execution/ethereum/db/offset_trie_db.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/nibble.h>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <functional>
#include <limits>
#include <optional>
#include <span>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace mpt_witness
{
    NodeId TrieStore::read_root(byte_string_view const blob)
    {
        unsigned char const *const base = blob.data();
        size_t const len = blob.size();
        MONAD_ASSERT(len >= HEADER_LEN);
        MONAD_ASSERT(
            base[0] == 'M' && base[1] == 'Z' && base[2] == 'W' &&
            base[3] == 0x01);
        // Keep blob offsets and overlay ids in disjoint halves of the NodeId
        // space (blob < OVERLAY_BASE, fresh ids >= OVERLAY_BASE). Bounding the
        // blob size bounds every offset. Real witnesses are ~MBs; this only
        // rejects a pathological >=2 GiB blob.
        MONAD_ASSERT(len <= OVERLAY_BASE);
        uint32_t const root_off = rd_u32(base + 4);
        MONAD_ASSERT(
            root_off == 0 || (root_off >= HEADER_LEN && root_off < len));
        // Empty trie: OVERLAY_BASE (the first fresh overlay id) is a stable,
        // mutable sentinel root that upsert_node materialises in place; the
        // ctor reserves it by advancing next_id_ past it.
        return root_off == 0 ? NodeId{OVERLAY_BASE} : NodeId{root_off};
    }

    TrieStore::TrieStore(byte_string_view const blob)
        : root{read_root(blob)}
        , blob_(blob)
    {
        unsigned char const *const base = blob_.data();

        // Prime hashes bottom-up over the blob's nodes (children precede
        // parents), rejecting any node whose extent leaves the region.
        unsigned char const *const region_end = blob_.end();
        NodeViewBase node{base + HEADER_LEN};
        while (node.bytes() < region_end) {
            unsigned char const *const node_end = node.end();
            MONAD_ASSERT(node_end <= region_end); // node fits the region
            prime_node(node);
            node = NodeViewBase{node_end};
        }
        MONAD_ASSERT(node.bytes() == region_end); // nodes tile exactly

        // Empty trie: reserve the sentinel root id so fresh_id never reuses it.
        if (is_overlay_id(root)) {
            next_id_ = NodeId{static_cast<uint32_t>(root) + 1};
        }
    }

    void TrieStore::prime_node(NodeViewBase const node)
    {
        auto const id = static_cast<NodeId>(
            static_cast<uint32_t>(node.bytes() - blob_.data()));
        if (node.tag() == DIGEST) {
            hashes_.emplace(id, DigestView{node}.hash());
            return;
        }
        unsigned char buf[MAX_NODE_RLP];
        node_rlp_span const rem =
            encode_rlp<true>(node, node_rlp_span{buf}); // priming pass
        // Only hash-referenced nodes (canonical RLP >= 32 B) are cached;
        // smaller nodes are inlined by their parent, so caching their hash
        // would make child_ref emit a 32-byte ref where the trie inlines it.
        if (rem.rlp_size() >= 32) {
            bytes32_t h;
            keccak256(rem.rlp_data(), rem.rlp_size(), h.bytes);
            hashes_.emplace(id, h);
        }
    }

    std::optional<NodeViewBase>
    TrieStore::find_original(NodeId id, mpt::NibblesView key) const
    {
        std::optional<NodeViewBase> found = std::nullopt;
        while (id != NULL_ID) {
            id = match(
                get_original(id),
                Cases{
                    [&](BranchView b) -> NodeId {
                        if (key.nibble_size() == 0) { // no value at a branch
                            return NULL_ID;
                        }
                        NodeId const next = b.child(key.get(0));
                        key = key.substr(1);
                        return next;
                    },
                    [&](ExtView e) -> NodeId {
                        mpt::NibblesView const ep = e.path();
                        if (!key.starts_with(ep)) {
                            return NULL_ID;
                        }
                        key = key.substr(ep.nibble_size());
                        return e.child();
                    },
                    [&](AcctLeafView l) -> NodeId {
                        if (l.path() == key) {
                            found = std::optional<NodeViewBase>{l};
                        }
                        return NULL_ID;
                    },
                    [&](StorageLeafView l) -> NodeId {
                        if (l.path() == key) {
                            found = std::optional<NodeViewBase>{l};
                        }
                        return NULL_ID;
                    },
                    [&](DigestView) -> NodeId {
                        MONAD_ABORT("incomplete witness: lookup hit a Digest");
                    },
                });
        }
        return found;
    }

    bytes32_t TrieStore::hash(NodeId const id)
    {
        if (!exists(id)) {
            return NULL_ROOT;
        }
        if (auto const it = hashes_.find(id); it != hashes_.end()) {
            return it->second;
        }
        NodeViewBase const node = get_current(id);
        bytes32_t h;
        if (node.tag() == DIGEST) {
            h = DigestView{node}.hash();
        }
        else {
            unsigned char buf[MAX_NODE_RLP];
            node_rlp_span const rem = encode_rlp(node, node_rlp_span{buf});
            // RLP occupies the tail: [rem.end(), buf_end).
            keccak256(rem.rlp_data(), rem.rlp_size(), h.bytes);
        }
        hashes_.emplace(id, h);
        return h;
    }

    bytes32_t TrieStore::state_root()
    {
        return hash(root);
    }

    template <bool priming_pass>
    TrieStore::node_rlp_span
    TrieStore::child_ref(NodeId const id, TrieStore::node_rlp_span dest)
    {
        if (id == NULL_ID) {
            dest.back() = 0x80; // RLP empty string
            return dest.shrink(1);
        }
        // A 32-byte hash reference is the RLP string of the hash (exactly 33 B:
        // 0xa0 + 32, no length prefix) — write it straight into the tail.
        auto const hash_ref = [&](bytes32_t const &h) {
            rlp::encode_string(dest.last(33), byte_string_view{h.bytes, 32});
            return dest.shrink(33);
        };
        if (auto const it = hashes_.find(id); it != hashes_.end()) {
            return hash_ref(it->second);
        }
        // Pre-state (priming) reads bound-check and resolve against the blob;
        // current reads consult the overlay first.
        NodeViewBase const node = [&]() -> NodeViewBase {
            if constexpr (priming_pass) {
                MONAD_ASSERT(static_cast<uint32_t>(id) < blob_.size());
                return get_original(id);
            }
            else {
                return get_current(id);
            }
        }();
        if (node.tag() == DIGEST) {
            bytes32_t const h = DigestView{node}.hash();
            hashes_.emplace(id, h);
            return hash_ref(h);
        }
        unsigned char scratch[MAX_NODE_RLP];
        node_rlp_span const rem =
            encode_rlp<priming_pass>(node, node_rlp_span{scratch});
        unsigned char const *const child_rlp = rem.rlp_data();
        size_t const child_rlp_len = rem.rlp_size();
        if (child_rlp_len < 32) {
            std::memcpy(
                dest.last(child_rlp_len).data(), child_rlp, child_rlp_len);
            return dest.shrink(child_rlp_len);
        }
        // A pre-state (blob) node this large is hash-referenced, so prime()
        // cached it bottom-up before any parent could reference it. Reaching
        // here on a cache miss means the parent held a forward/garbage offset.
        if constexpr (priming_pass) {
            MONAD_ABORT(
                "offset trie: unprimed hash-referenced node (bad offset)");
        }
        bytes32_t h;
        keccak256(child_rlp, child_rlp_len, h.bytes);
        hashes_.emplace(id, h);
        return hash_ref(h);
    }

    template <bool priming_pass>
    TrieStore::node_rlp_span TrieStore::encode_rlp(
        NodeViewBase const node, TrieStore::node_rlp_span dest)
    {
        // Compact-encode `path` straight into d's tail as an RLP string; return
        // d shrunk. The compact form is clen = nibble_size/2 + 1 bytes (<= 33,
        // always a short string): write it directly, then prepend the
        // 0x80+path_len prefix. When path_len == 1 the single byte is <= 0x3F,
        // so it is already its own RLP and no prefix is added.
        auto const put_path = [](TrieStore::node_rlp_span d,
                                 mpt::NibblesView const path,
                                 bool const terminating) {
            size_t const path_len = path.nibble_size() / 2 + 1;
            mpt::compact_encode_raw(d.last(path_len).data(), path, terminating);
            d = d.shrink(path_len);
            if (path_len > 1) {
                d.back() = static_cast<unsigned char>(0x80 + path_len);
                d = d.shrink(1);
            }
            return d;
        };
        // Prepend the list header for payload [s.end(), dest.end()); return the
        // final span. encode_list_prefix can transiently write up to 8 bytes,
        // so build the header in a local and copy only its real length into
        // place.
        auto const wrap = [&](TrieStore::node_rlp_span const s) {
            size_t const payload_len = s.rlp_size();
            unsigned char hdr[9];
            auto const rest = rlp::encode_list_prefix(
                std::span<unsigned char>{hdr}, payload_len);
            size_t const hdr_len = sizeof(hdr) - rest.size();
            std::memcpy(s.last(hdr_len).data(), hdr, hdr_len);
            return s.shrink(hdr_len);
        };
        return node_rlp_span{match(
            node,
            Cases{
                [&](BranchView b) -> std::span<unsigned char> {
                    dest.back() =
                        0x80; // empty branch value — last list element
                    dest = dest.shrink(1);
                    for (int i = 15; i >= 0; --i) {
                        dest = child_ref<priming_pass>(
                            b.child(static_cast<unsigned>(i)), dest);
                    }
                    return wrap(dest);
                },
                [&](ExtView e) -> std::span<unsigned char> {
                    // child ref — last element
                    dest = child_ref<priming_pass>(e.child(), dest);
                    dest = put_path(dest, e.path(), /*terminating=*/false);
                    return wrap(dest);
                },
                [&](AcctLeafView l) -> std::span<unsigned char> {
                    // value = the stored account RLP, wrapped as a string
                    auto const account_rlp = l.account_rlp();
                    size_t const account_len = rlp::string_length(account_rlp);
                    rlp::encode_string(dest.last(account_len), account_rlp);
                    dest = dest.shrink(account_len);
                    dest = put_path(dest, l.path(), /*terminating=*/true);
                    return wrap(dest);
                },
                [&](StorageLeafView l) -> std::span<unsigned char> {
                    bytes32_t const v = l.value();
                    // storage value = rlp(zeroless(slot)), itself wrapped again
                    // as the leaf's value string: write the inner rlp(zl) into
                    // dest's tail, then prepend the outer string prefix in
                    // place.
                    auto const val =
                        rlp::zeroless_view(to_byte_string_view(v.bytes));
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
                    dest = put_path(dest, l.path(), /*terminating=*/true);
                    return wrap(dest);
                },
                [&](DigestView) -> std::span<unsigned char> {
                    MONAD_ABORT(
                        "encode_rlp() on a Digest (should short-circuit)");
                },
            })};
    }

    // ── mutation — typed byte builders (§4 layout) ───────────────────────────
    namespace
    {
        // Append `v` little-endian, matching rd_u32/rd_u16 on rv64im/x86.
        void append_u32(byte_string &b, uint32_t const v)
        {
            static_assert(std::endian::native == std::endian::little);
            b.append(reinterpret_cast<unsigned char const *>(&v), sizeof(v));
        }

        void append_u16(byte_string &b, uint16_t const v)
        {
            static_assert(std::endian::native == std::endian::little);
            b.append(reinterpret_cast<unsigned char const *>(&v), sizeof(v));
        }

        // Append a path as nodes store it: a 1-byte nibble count then
        // ceil(nlen/2) packed nibbles, left-aligned (nibble 0 in the high
        // nibble of the first byte) — exactly what path_view reads back.
        void append_path(byte_string &b, mpt::NibblesView const path)
        {
            unsigned const nlen = path.nibble_size();
            b.push_back(static_cast<unsigned char>(nlen));
            size_t const start = b.size();
            b.resize(start + (nlen + 1) / 2, 0);
            for (unsigned i = 0; i < nlen; ++i) {
                set_nibble(b.data() + start, i, path.get(i));
            }
        }

        unsigned
        common_prefix_length(mpt::NibblesView const a, mpt::NibblesView const b)
        {
            unsigned const n = std::min(a.nibble_size(), b.nibble_size());
            for (unsigned i = 0; i < n; ++i) {
                if (a.get(i) != b.get(i)) {
                    return i;
                }
            }
            return n;
        }
    }

    void append_branch(byte_string &out, std::array<NodeId, 16> const &children)
    {
        out.reserve(out.size() + 1 + 16 * 4);
        out.push_back(BRANCH);
        for (NodeId const c : children) {
            append_u32(out, static_cast<uint32_t>(c));
        }
    }

    void append_ext(
        byte_string &out, mpt::NibblesView const path, NodeId const child)
    {
        out.push_back(EXT);
        append_path(out, path);
        append_u32(out, static_cast<uint32_t>(child));
    }

    void append_storage(
        byte_string &out, mpt::NibblesView const path, bytes32_t const &value)
    {
        out.push_back(LEAF_STORAGE);
        append_path(out, path);
        out.append(value.bytes, 32);
    }

    void append_acct_raw(
        byte_string &out, mpt::NibblesView const path,
        byte_string_view const acct_rlp, NodeId const storage)
    {
        MONAD_ASSERT(acct_rlp.size() <= std::numeric_limits<uint16_t>::max());
        out.push_back(LEAF_ACCT);
        append_path(out, path);
        append_u16(out, static_cast<uint16_t>(acct_rlp.size()));
        out.append(acct_rlp.data(), acct_rlp.size());
        append_u32(out, static_cast<uint32_t>(storage));
    }

    void append_digest(byte_string &out, bytes32_t const &hash)
    {
        out.push_back(DIGEST);
        out.append(hash.bytes, 32);
    }

    NodeId TrieStore::fresh_id()
    {
        NodeId const fresh = next_id_;
        next_id_ = NodeId{static_cast<uint32_t>(next_id_) + 1};
        return fresh;
    }

    NodeId TrieStore::put_node(NodeId const id, byte_string node)
    {
        if (id == NULL_ID) {
            NodeId const fresh = fresh_id();
            overlay_[fresh] = std::move(node);
            return fresh;
        }
        hashes_.erase(id); // bytes changed; the cached hash is stale
        overlay_[id] = std::move(node);
        return id;
    }

    NodeId TrieStore::put_branch(
        NodeId const id, std::array<NodeId, 16> const &children)
    {
        byte_string node;
        append_branch(node, children);
        return put_node(id, std::move(node));
    }

    NodeId TrieStore::put_ext(
        NodeId const id, mpt::NibblesView const path, NodeId const child)
    {
        byte_string node;
        append_ext(node, path, child);
        return put_node(id, std::move(node));
    }

    NodeId TrieStore::put_storage(
        NodeId const id, mpt::NibblesView const path, bytes32_t const &value)
    {
        byte_string node;
        append_storage(node, path, value);
        return put_node(id, std::move(node));
    }

    NodeId TrieStore::put_acct_raw(
        NodeId const id, mpt::NibblesView const path,
        byte_string_view const acct_rlp, NodeId const storage)
    {
        byte_string node;
        append_acct_raw(node, path, acct_rlp, storage);
        return put_node(id, std::move(node));
    }

    NodeId TrieStore::put_acct(
        NodeId const id, mpt::NibblesView const path, Account const &acct,
        bytes32_t const &storage_root, NodeId const storage)
    {
        return put_acct_raw(
            id, path, rlp::encode_account(acct, storage_root), storage);
    }

    Tag TrieStore::fold_ext_node_path_maybe(
        NodeId const ext_parent, mpt::NibblesView const prefix,
        NodeViewBase const child)
    {
        MONAD_ASSERT(ext_parent != NULL_ID);

        return match(
            child,
            Cases{
                // A branch can't absorb a path prefix — caller wraps it in ext.
                [&](BranchView) { return EXT; },
                [&](ExtView e) {
                    put_ext(
                        ext_parent, mpt::concat(prefix, e.path()), e.child());
                    return EXT;
                },
                [&](StorageLeafView l) {
                    put_storage(
                        ext_parent, mpt::concat(prefix, l.path()), l.value());
                    return LEAF_STORAGE;
                },
                [&](AcctLeafView l) {
                    put_acct_raw(
                        ext_parent,
                        mpt::concat(prefix, l.path()),
                        l.account_rlp(),
                        l.storage());
                    return LEAF_ACCT;
                },
                [&](DigestView) -> Tag {
                    MONAD_ABORT("incomplete witness: collapse hit a Digest");
                },
            });
    }

    std::pair<NodeId, mpt::Nibbles>
    TrieStore::upsert_node(NodeId const id, mpt::NibblesView const key)
    {
        if (id == NULL_ID) { // empty slot -> new leaf
            return {fresh_id(), mpt::Nibbles{key}};
        }
        // A non-null id is always materialised in production (the root exists;
        // the empty-trie root is a test-only sentinel the caller fills in
        // place). Debug-only so upsert pays no exists() penalty in prod.
        MONAD_DEBUG_ASSERT(exists(id));
        hashes_.erase(id); // dirtied along the descent
        // Leaf split/overwrite, shared by both leaf types. Only re-emitting the
        // displaced old leaf differs (`reput_old`): storage keeps its value, an
        // account its acct_rlp + storage. The caller reads the old leaf's
        // fields into reput_old's captures first, since views die at the first
        // put_*.
        auto const split_leaf =
            [&](mpt::NibblesView const path,
                auto const &reput_old) -> std::pair<NodeId, mpt::Nibbles> {
            if (path == key) { // exact match -> overwrite (reuse id + its path)
                return {id, mpt::Nibbles{key}};
            }
            // old leaf + new key meet at a fresh branch, wrapped in an
            // extension for their shared prefix.
            unsigned const cp = common_prefix_length(path, key);
            MONAD_ASSERT(cp < path.nibble_size() && cp < key.nibble_size());
            std::array<NodeId, 16> children{};
            children[path.get(cp)] = reput_old(path.substr(cp + 1));
            NodeId const leaf = fresh_id();
            children[key.get(cp)] = leaf;
            if (cp > 0) {
                NodeId const branch = put_branch(NULL_ID, children);
                put_ext(id, key.substr(0, cp), branch);
            }
            else {
                put_branch(id, children);
            }
            return {leaf, mpt::Nibbles{key.substr(cp + 1)}};
        };

        return match(
            get_current(id),
            Cases{
                [&](StorageLeafView l) -> std::pair<NodeId, mpt::Nibbles> {
                    bytes32_t const v = l.value();
                    return split_leaf(l.path(), [&](mpt::NibblesView const np) {
                        return put_storage(NULL_ID, np, v);
                    });
                },
                [&](AcctLeafView l) -> std::pair<NodeId, mpt::Nibbles> {
                    byte_string const rlp{l.account_rlp()};
                    NodeId const st = l.storage();
                    return split_leaf(l.path(), [&](mpt::NibblesView const np) {
                        return put_acct_raw(NULL_ID, np, rlp, st);
                    });
                },
                [&](ExtView e) -> std::pair<NodeId, mpt::Nibbles> {
                    mpt::Nibbles const p{e.path()};
                    mpt::NibblesView const path{p};
                    NodeId const child = e.child();
                    unsigned const cp = common_prefix_length(path, key);
                    if (cp == path.nibble_size()) { // full prefix -> descend
                        return upsert_node(child, key.substr(cp));
                    }
                    // diverge mid-extension
                    std::array<NodeId, 16> children{};
                    children[path.get(cp)] =
                        (cp + 1 < path.nibble_size())
                            ? put_ext(NULL_ID, path.substr(cp + 1), child)
                            : child;
                    NodeId const leaf = fresh_id();
                    children[key.get(cp)] = leaf;

                    if (cp > 0) {
                        NodeId const branch = put_branch(NULL_ID, children);
                        put_ext(id, key.substr(0, cp), branch);
                    }
                    else {
                        put_branch(id, children);
                    }
                    return {leaf, mpt::Nibbles{key.substr(cp + 1)}};
                },
                [&](BranchView b) -> std::pair<NodeId, mpt::Nibbles> {
                    MONAD_ASSERT(key.nibble_size() > 0); // never ends at branch
                    unsigned const nib = key.get(0);
                    std::array<NodeId, 16> children = b.children();
                    NodeId const child = children[nib];
                    // Recurse into the slot: a NULL_ID child lets upsert_node
                    // allocate the leaf; an existing child keeps its stable id.
                    // Only rewrite the branch when a previously-empty slot
                    // fills.
                    auto const result = upsert_node(child, key.substr(1));
                    if (child == NULL_ID) {
                        children[nib] = result.first;
                        put_branch(id, children);
                    }
                    return result;
                },
                [&](DigestView) -> std::pair<NodeId, mpt::Nibbles> {
                    MONAD_ABORT("incomplete witness: upsert hit a Digest");
                },
            });
    }

    TrieStore::EraseResult
    TrieStore::erase_node(NodeId const id, mpt::NibblesView const key)
    {
        if (id == NULL_ID) { // absent
            return TrieStore::EraseResult::Unmodified;
        }
        return match(
            get_current(id),
            Cases{
                [&](StorageLeafView l) -> TrieStore::EraseResult {
                    return l.path() == key ? TrieStore::EraseResult::Erased
                                           : TrieStore::EraseResult::Unmodified;
                },
                [&](AcctLeafView l) -> TrieStore::EraseResult {
                    return l.path() == key ? TrieStore::EraseResult::Erased
                                           : TrieStore::EraseResult::Unmodified;
                },
                [&](ExtView e) -> TrieStore::EraseResult {
                    NodeId const child_id = e.child();
                    MONAD_ASSERT(child_id != NULL_ID);
                    mpt::Nibbles const p{e.path()};
                    mpt::NibblesView const path{p};
                    unsigned const cp = common_prefix_length(path, key);
                    if (cp < path.nibble_size()) { // key not under this ext
                        return TrieStore::EraseResult::Unmodified;
                    }
                    auto const erase_child =
                        erase_node(child_id, key.substr(cp));
                    if (erase_child ==
                        TrieStore::EraseResult::Erased) { // child gone -> ext
                                                          // gone
                        return TrieStore::EraseResult::Erased;
                    }
                    if (erase_child == TrieStore::EraseResult::Unmodified) {
                        return TrieStore::EraseResult::Unmodified;
                    }
                    // child survived; fold the ext path into it if it collapsed
                    // to a leaf/ext, but keep `id` of the ext node
                    hashes_.erase(id);
                    return fold_ext_node_path_maybe(
                               id, path, get_current(child_id)) == EXT
                               ? TrieStore::EraseResult::SameShape
                               : TrieStore::EraseResult::NewShape;
                },
                [&](BranchView b) -> TrieStore::EraseResult {
                    MONAD_ASSERT(key.nibble_size() > 0);
                    unsigned const branch = key.get(0);
                    std::array<NodeId, 16> children = b.children();
                    NodeId const child = children[branch];
                    if (child == NULL_ID) {
                        return TrieStore::EraseResult::Unmodified;
                    }
                    auto const erase_child =
                        erase_node(children[branch], key.substr(1));
                    if (erase_child == TrieStore::EraseResult::Unmodified) {
                        return TrieStore::EraseResult::Unmodified;
                    }
                    hashes_.erase(id);
                    if (erase_child == TrieStore::EraseResult::Erased) {
                        children[branch] = NULL_ID;
                    }
                    unsigned count = 0;
                    unsigned single = 0;
                    for (unsigned i = 0; i < 16 && count < 2; ++i) {
                        if (children[i] != NULL_ID) {
                            ++count;
                            single = i;
                        }
                    }
                    if (count == 0) {
                        return TrieStore::EraseResult::Erased;
                    }
                    if (count == 1) {
                        // collapse: fold the branch nibble into the sole child;
                        // if that child is itself a branch, wrap it in a
                        // one-nibble extension instead.
                        mpt::Nibbles const child_path =
                            mpt::concat(static_cast<unsigned char>(single));
                        NodeViewBase const child =
                            get_current(children[single]);

                        if (child.tag() == BRANCH) {
                            put_ext(
                                id,
                                mpt::NibblesView{child_path},
                                children[single]);
                            return TrieStore::EraseResult::NewShape;
                        }
                        else {
                            return fold_ext_node_path_maybe(
                                       id,
                                       mpt::NibblesView{child_path},
                                       child) == BRANCH
                                       ? TrieStore::EraseResult::SameShape
                                       : TrieStore::EraseResult::NewShape;
                        }
                    }
                    else {
                        put_branch(id, children); // >=2 survivors: stays
                        return TrieStore::EraseResult::SameShape;
                    }
                },
                [&](DigestView) -> TrieStore::EraseResult {
                    MONAD_ABORT("incomplete witness: erase hit a Digest");
                },
            });
    }
}

// ── OffsetTrieDb ────────────────────────────────────────────────────────────

std::optional<Account> OffsetTrieDb::read_account(Address const &addr)
{
    auto const key = keccak256(addr.bytes);
    auto const leaf = store_.find_original(store_.root, mpt::NibblesView{key});
    if (!leaf) {
        return std::nullopt;
    }
    return mpt_witness::AcctLeafView{*leaf}.account();
}

bytes32_t OffsetTrieDb::read_storage(
    Address const &addr, Incarnation, bytes32_t const &slot)
{
    auto const akey = keccak256(addr.bytes);
    auto const aleaf =
        store_.find_original(store_.root, mpt::NibblesView{akey});
    if (!aleaf) {
        return {};
    }
    auto const sroot = mpt_witness::AcctLeafView{*aleaf}.storage();
    if (sroot == mpt_witness::NULL_ID) {
        return {};
    }
    auto const skey = keccak256(slot.bytes);
    auto const sleaf = store_.find_original(sroot, mpt::NibblesView{skey});
    if (!sleaf) {
        return {};
    }
    return mpt_witness::StorageLeafView{*sleaf}.value();
}

void OffsetTrieDb::commit(
    bytes32_t const &, CommitBuilder &, BlockHeader const &header,
    StateDeltas const &deltas,
    std::function<void(BlockHeader &)> populate_header_fn)
{
    using namespace mpt_witness;
    block_number_ = header.number;

    // Pass 1: inserts and updates — accounts present in the post-state. Mirrors
    // PartialTrieDb::commit (partial_trie_db.cpp), with the storage sub-root
    // threaded through the put_* builders instead of a live leaf reference.
    for (auto const &[addr, delta] : deltas) {
        auto const &new_account = delta.account.second;
        if (!new_account) {
            continue;
        }
        auto const acct_key = keccak256(addr.bytes);
        auto const [leaf, leaf_path] =
            store_.upsert_node(store_.root, mpt::NibblesView{acct_key});
        NodeId storage = [&] {
            if (store_.exists(leaf)) {
                AcctLeafView const acc{store_.get_current(leaf)};
                return acc.storage();
            }
            else {
                return NULL_ID;
            }
        }();

        // Incarnation bump (destroy + recreate in-block): wipe old storage.
        if (delta.account.first.has_value() &&
            delta.account.first->incarnation != new_account->incarnation) {
            storage = NULL_ID;
        }

        // Storage deltas: upserts first, then deletions (as in the reference).
        for (auto const &[slot, sdelta] : delta.storage) {
            if (sdelta.second != bytes32_t{}) {
                auto const slot_key = keccak256(slot.bytes);
                auto const [sleaf, sleaf_path] =
                    store_.upsert_node(storage, mpt::NibblesView{slot_key});
                if (storage == NULL_ID) {
                    storage = sleaf; // first slot into empty storage: the leaf
                                     // is the sub-root
                }
                store_.put_storage(sleaf, sleaf_path, sdelta.second);
            }
        }
        for (auto const &[slot, sdelta] : delta.storage) {
            if (sdelta.second == bytes32_t{} && sdelta.first != bytes32_t{}) {
                auto const slot_key = keccak256(slot.bytes);
                if (store_.erase_node(storage, mpt::NibblesView{slot_key}) ==
                    TrieStore::EraseResult::Erased) {
                    storage = NULL_ID;
                };
            }
        }

        // Bake the freshly computed storage root into the account leaf.
        bytes32_t const storage_root = store_.hash(storage);
        store_.put_acct(
            leaf,
            mpt::NibblesView{leaf_path},
            *new_account,
            storage_root,
            storage);
    }

    // Pass 2: deletions — accounts absent in the post-state but present before.
    for (auto const &[addr, delta] : deltas) {
        if (delta.account.second || !delta.account.first) {
            continue;
        }
        auto const acct_key = keccak256(addr.bytes);
        store_.erase_node(store_.root, mpt::NibblesView{acct_key});
    }

    last_committed_header_ = header;
    MONAD_ASSERT(populate_header_fn);
    populate_header_fn(last_committed_header_);
}

MONAD_NAMESPACE_END
