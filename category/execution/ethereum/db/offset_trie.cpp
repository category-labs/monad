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
#include <category/core/keccak.hpp>
#include <category/core/nibble.h>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <limits>
#include <span>
#include <utility>

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
    MONAD_ASSERT(len <= OVERLAY_BASE);
    uint32_t const root_off = read_u32(base + 4);
    MONAD_ASSERT(root_off == 0 || (root_off >= HEADER_LEN && root_off < len));
    return NodeId{root_off};
}

OffsetTrie::OffsetTrie(byte_string_view const blob)
    : root{read_root(blob)}
    , blob_(blob)
{
    unsigned char const *const base = blob_.data();

    // Prime hashes bottom-up over the blob's nodes (children precede
    // parents), rejecting any node whose extent leaves the region.
    unsigned char const *const region_end = blob_.end();
    NodeViewBase node{base + HEADER_LEN};
    while (node.bytes() < region_end) {
        match(
            node,
            Cases{
                [](NullView) {},
                [](DigestView) {},
                [&](auto) {
                    unsigned char buf[MAX_NODE_RLP];
                    node_rlp_span const rem = encode_rlp<true>(
                        node, node_rlp_span{buf}); // priming pass
                    // Only hash-referenced nodes (canonical RLP >= 32 B)
                    // are cached; smaller nodes are inlined by their
                    // parent, so caching their hash would make child_ref
                    // emit a 32-byte ref where the trie inlines it.
                    if (rem.rlp_size() >= 32) {
                        bytes32_t h;
                        keccak256(rem.rlp_data(), rem.rlp_size(), h.bytes);

                        auto const id = static_cast<NodeId>(
                            static_cast<uint32_t>(node.bytes() - blob_.data()));
                        hashes_.emplace(id, h);
                    }
                }});

        node = NodeViewBase{node.end()};
    }
    MONAD_ASSERT(node.bytes() == region_end); // nodes tile exactly
}

NodeViewBase OffsetTrie::find_original(NodeId id, NibblesView key) const
{
    NodeViewBase found = empty();
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
                if (auto const it = hashes_.find(id); it != hashes_.end()) {
                    return it->second;
                }

                unsigned char buf[MAX_NODE_RLP];
                node_rlp_span const rem = encode_rlp(node, node_rlp_span{buf});
                bytes32_t h;
                // RLP occupies the tail: [rem.end(), buf_end).
                keccak256(rem.rlp_data(), rem.rlp_size(), h.bytes);

                hashes_.emplace(id, h);
                return h;
            }});
}

bytes32_t OffsetTrie::state_root()
{
    return hash(root);
}

template <bool priming_pass>
OffsetTrie::node_rlp_span
OffsetTrie::child_ref(NodeId const id, OffsetTrie::node_rlp_span dest)
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
    MONAD_ASSERT(node.tag() != EMPTY);
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
        std::memcpy(dest.last(child_rlp_len).data(), child_rlp, child_rlp_len);
        return dest.shrink(child_rlp_len);
    }
    // A pre-state (blob) node this large is hash-referenced, so prime()
    // cached it bottom-up before any parent could reference it. Reaching
    // here on a cache miss means the parent held a forward/garbage offset.
    if constexpr (priming_pass) {
        MONAD_ABORT("offset trie: unprimed hash-referenced node (bad offset)");
    }
    bytes32_t h;
    keccak256(child_rlp, child_rlp_len, h.bytes);
    hashes_.emplace(id, h);
    return hash_ref(h);
}

template <bool priming_pass>
OffsetTrie::node_rlp_span
OffsetTrie::encode_rlp(NodeViewBase const node, OffsetTrie::node_rlp_span dest)
{
    MONAD_DEBUG_ASSERT(node.tag() != EMPTY && node.tag() != DIGEST);
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
    // Prepend the list header for payload [s.end(), dest.end()); return the
    // final span. encode_list_prefix can transiently write up to 8 bytes,
    // so build the header in a local and copy only its real length into
    // place.
    auto const wrap = [](OffsetTrie::node_rlp_span const s) {
        size_t const payload_len = s.rlp_size();
        unsigned char hdr[9];
        auto const rest =
            rlp::encode_list_prefix(std::span<unsigned char>{hdr}, payload_len);
        size_t const hdr_len = sizeof(hdr) - rest.size();
        std::memcpy(s.last(hdr_len).data(), hdr, hdr_len);
        return s.shrink(hdr_len);
    };
    return node_rlp_span{match(
        node,
        Cases{
            [&, wrap](BranchView b) -> std::span<unsigned char> {
                dest.back() = 0x80; // empty branch value — last list element
                dest = dest.shrink(1);
                for (int i = 15; i >= 0; --i) {
                    dest = child_ref<priming_pass>(
                        b.child(static_cast<unsigned>(i)), dest);
                }
                return wrap(dest);
            },
            [&, encode_path, wrap](ExtView e) -> std::span<unsigned char> {
                // child ref — last element
                dest = child_ref<priming_pass>(e.child(), dest);
                dest = encode_path(dest, e.path(), /*terminating=*/false);
                return wrap(dest);
            },
            [&, encode_path, wrap](
                AccountLeafView l) -> std::span<unsigned char> {
                // value = the stored account RLP, wrapped as a string
                auto const account_rlp = l.account_rlp();
                size_t const account_len = rlp::string_length(account_rlp);
                rlp::encode_string(dest.last(account_len), account_rlp);
                dest = dest.shrink(account_len);
                dest = encode_path(dest, l.path(), /*terminating=*/true);
                return wrap(dest);
            },
            [&, encode_path, wrap](
                StorageLeafView l) -> std::span<unsigned char> {
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
                    dest.back() = static_cast<unsigned char>(0x80 + val_len);
                    dest = dest.shrink(1);
                }
                dest = encode_path(dest, l.path(), /*terminating=*/true);
                return wrap(dest);
            },
            [](DigestView) -> std::span<unsigned char> { std::unreachable(); },
            [](NullView) -> std::span<unsigned char> { std::unreachable(); },
        })};
}

// ── mutation — typed byte builders (§4 layout) ───────────────────────────────
namespace
{
    // Append `v` little-endian, matching read_u32/read_u16 on rv64im/x86.
    void append_node_id(byte_string &b, NodeId const v)
    {
        static_assert(std::endian::native == std::endian::little);
        b.append(reinterpret_cast<unsigned char const *>(&v), sizeof(v));
    }

    void append_rlp(byte_string &b, byte_string_view const v)
    {
        static_assert(std::endian::native == std::endian::little);
        MONAD_ASSERT(v.size() <= std::numeric_limits<uint16_t>::max());
        auto const len = static_cast<uint16_t>(v.size());
        b.append(reinterpret_cast<unsigned char const *>(&len), sizeof(len));
        b.append(v.data(), v.size());
    }

    // Append a path as nodes store it: a 1-byte nibble count then
    // ceil(nlen/2) packed nibbles, left-aligned (nibble 0 in the high
    // nibble of the first byte) — exactly what path_view reads back.
    void append_path(byte_string &b, NibblesView const path)
    {
        unsigned const nlen = path.nibble_size();
        // path_nlen reads the count back as a single byte, so a truncated
        // one would desynchronise the node stream (as in append_rlp).
        MONAD_ASSERT(nlen <= std::numeric_limits<unsigned char>::max());
        b.push_back(static_cast<unsigned char>(nlen));
        size_t const start = b.size();
        b.resize(start + (nlen + 1) / 2, 0);
        for (unsigned i = 0; i < nlen; ++i) {
            set_nibble(b.data() + start, i, path.get(i));
        }
    }

    unsigned common_prefix_length(NibblesView const a, NibblesView const b)
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

void append_acct_raw(
    byte_string &out, NibblesView const path, byte_string_view const acct_rlp,
    NodeId const storage)
{
    out.push_back(LEAF_ACCT);
    append_node_id(out, storage);
    append_path(out, path);
    append_rlp(out, acct_rlp);
}

void append_digest(byte_string &out, bytes32_t const &hash)
{
    out.push_back(DIGEST);
    out.append(hash.bytes, 32);
}

NodeId OffsetTrie::fresh_id()
{
    NodeId const fresh = next_id_;
    next_id_ = NodeId{static_cast<uint32_t>(next_id_) + 1};
    return fresh;
}

NodeId OffsetTrie::put_node(NodeId const id, byte_string node)
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

NodeId
OffsetTrie::put_branch(NodeId const id, std::array<NodeId, 16> const &children)
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

NodeId OffsetTrie::put_acct_raw(
    NodeId const id, NibblesView const path, byte_string_view const acct_rlp,
    NodeId const storage)
{
    byte_string node;
    append_acct_raw(node, path, acct_rlp, storage);
    return put_node(id, std::move(node));
}

NodeId OffsetTrie::put_acct(
    NodeId const id, NibblesView const path, Account const &acct,
    bytes32_t const &storage_root, NodeId const storage)
{
    return put_acct_raw(
        id, path, rlp::encode_account(acct, storage_root), storage);
}

Tag OffsetTrie::fold_ext_node_path_maybe(
    NodeId const ext_parent, NibblesView const prefix, NodeViewBase const child)
{
    MONAD_ASSERT(ext_parent != NULL_ID);
    MONAD_DEBUG_ASSERT(child.tag() != EMPTY);

    return match(
        child,
        Cases{
            // A branch can't absorb a path prefix — caller wraps it in ext.
            [&](BranchView) { return EXT; },
            [&](ExtView e) {
                put_ext(ext_parent, concat(prefix, e.path()), e.child());
                return EXT;
            },
            [&](StorageLeafView l) {
                put_storage(ext_parent, concat(prefix, l.path()), l.value());
                return LEAF_STORAGE;
            },
            [&](AccountLeafView l) {
                put_acct_raw(
                    ext_parent,
                    concat(prefix, l.path()),
                    l.account_rlp(),
                    l.storage());
                return LEAF_ACCT;
            },
            [](DigestView) -> Tag {
                MONAD_ABORT("incomplete witness: collapse hit a Digest");
            },
            // Callers only fold a surviving child into its parent's path.
            [](NullView) -> Tag { std::unreachable(); },
        });
}

std::pair<NodeId, Nibbles>
OffsetTrie::upsert_node(NodeId const id, NibblesView const key)
{
    hashes_.erase(id); // dirtied along the descent
    // Leaf split/overwrite, shared by both leaf types. Only re-emitting the
    // displaced old leaf differs (`reput_old`): storage keeps its value, an
    // account its acct_rlp + storage. The caller reads the old leaf's
    // fields into reput_old's captures first, since views die at the first
    // put_*.
    auto const split_leaf =
        [&](NibblesView const path,
            auto const &reput_old) -> std::pair<NodeId, Nibbles> {
        if (path == key) { // exact match -> overwrite (reuse id + its path)
            return {id, Nibbles{key}};
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
        return {leaf, Nibbles{key.substr(cp + 1)}};
    };

    return match(
        get_current(id),
        Cases{
            [&](NullView) -> std::pair<NodeId, Nibbles> {
                // Empty slot (or an empty trie's root): a fresh leaf
                // holding the whole remaining key, which the caller
                // materialises.
                return {fresh_id(), Nibbles{key}};
            },
            [&](StorageLeafView l) -> std::pair<NodeId, Nibbles> {
                bytes32_t const v = l.value();
                return split_leaf(l.path(), [&](NibblesView const np) {
                    return put_storage(NULL_ID, np, v);
                });
            },
            [&](AccountLeafView l) -> std::pair<NodeId, Nibbles> {
                byte_string const rlp{l.account_rlp()};
                NodeId const st = l.storage();
                return split_leaf(l.path(), [&](NibblesView const np) {
                    return put_acct_raw(NULL_ID, np, rlp, st);
                });
            },
            [&](ExtView e) -> std::pair<NodeId, Nibbles> {
                Nibbles const p{e.path()};
                NibblesView const path{p};
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
                return {leaf, Nibbles{key.substr(cp + 1)}};
            },
            [&](BranchView b) -> std::pair<NodeId, Nibbles> {
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
            [&](DigestView) -> std::pair<NodeId, Nibbles> {
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
                hashes_.erase(id);
                NodeViewBase const child = get_current(child_id);
                return match(
                    child,
                    Cases{
                        [](NullView) -> OffsetTrie::EraseResult {
                            MONAD_ABORT("malformed trie: node not found");
                        },
                        [&](auto) {
                            return fold_ext_node_path_maybe(id, path, child) ==
                                           EXT
                                       ? OffsetTrie::EraseResult::SameShape
                                       : OffsetTrie::EraseResult::NewShape;
                        }});
            },
            [&](BranchView b) -> OffsetTrie::EraseResult {
                MONAD_ASSERT(key.nibble_size() > 0);
                unsigned const branch = key.get(0);
                std::array<NodeId, 16> children = b.children();
                NodeId const child = children[branch];
                if (child == NULL_ID) {
                    return OffsetTrie::EraseResult::Unmodified;
                }
                auto const erase_child =
                    erase_node(children[branch], key.substr(1));
                if (erase_child == OffsetTrie::EraseResult::Unmodified) {
                    return OffsetTrie::EraseResult::Unmodified;
                }
                hashes_.erase(id);
                if (erase_child == OffsetTrie::EraseResult::Erased) {
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
                    return OffsetTrie::EraseResult::Erased;
                }
                if (count == 1) {
                    // collapse: fold the branch nibble into the sole child;
                    // if that child is itself a branch, wrap it in a
                    // one-nibble extension instead.
                    Nibbles const child_path =
                        concat(static_cast<unsigned char>(single));
                    NodeViewBase const child = get_current(children[single]);
                    return match(
                        child,
                        Cases{
                            [](NullView) -> OffsetTrie::EraseResult {
                                MONAD_ABORT("malformed trie: node not found");
                            },
                            [&](BranchView) {
                                put_ext(
                                    id,
                                    NibblesView{child_path},
                                    children[single]);
                                return OffsetTrie::EraseResult::NewShape;
                            },
                            [&](auto) {
                                fold_ext_node_path_maybe(
                                    id, NibblesView{child_path}, child);
                                return OffsetTrie::EraseResult::NewShape;
                            }});
                }
                else {
                    put_branch(id, children); // >=2 survivors: stays
                    return OffsetTrie::EraseResult::SameShape;
                }
            },
            [&](DigestView) -> OffsetTrie::EraseResult {
                MONAD_ABORT("incomplete witness: erase hit a Digest");
            },
        });
}

MONAD_MPT_NAMESPACE_END
