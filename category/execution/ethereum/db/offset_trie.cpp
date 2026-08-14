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

namespace
{
    // Set (val = true) or clear (val = false) the bit for byte offset `off`
    template <bool val>
    void set_offset_value(std::span<uint64_t> const offsets, uint64_t const off)
    {
        uint64_t const bit = uint64_t{1} << (off & 63);
        if constexpr (val) {
            offsets[off >> 6] |= bit;
        }
        else {
            offsets[off >> 6] &= ~bit;
        }
    }
}

OffsetTrie::OffsetTrie(byte_string_view const blob)
    : blob_(blob)
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
    std::vector<uint64_t> node_offsets((blob_.size() + 63) / 64, 0);

    // A node's bit is set when the walk reaches it and cleared when a parent
    // claims it as a child.
    // A child whose bit is clear is either previously unseen/invalid or already
    // claimed by a different parent.
    auto const is_valid_offset = [&](NodeId c) {
        if (c == NULL_ID) {
            return;
        }
        uint64_t child_offset = static_cast<uint64_t>(c);
        MONAD_ASSERT(
            child_offset < blob_.size() &&
            (node_offsets[child_offset >> 6] &
             (uint64_t{1} << (child_offset & 63))));
        set_offset_value<false>(node_offsets, child_offset);
    };
    unsigned char rlp_buf[MAX_NODE_RLP];

    while (node.bytes() < region_end) {
        // checked_end asserts that the current node does not reach past the end
        // of the region
        auto next_offset =
            static_cast<uint64_t>(node.checked_end(region_end) - base);

        match(
            node,
            Cases{
                [&](BranchView b) {
                    // Validate the 16 children two at a time: a uint64_t load
                    // spans exactly one pair, low word first.
                    static_assert(std::endian::native == std::endian::little);
                    static_assert(
                        sizeof(uint64_t) == 2 * sizeof(node_id_wire_t));
                    unsigned char const *const p = b.payload();
                    uint64_t pair;
                    for (unsigned i = 0; i < 8; ++i) {
                        std::memcpy(&pair, p + i * sizeof(pair), sizeof(pair));
                        is_valid_offset(
                            NodeId{static_cast<node_id_wire_t>(pair)});
                        is_valid_offset(
                            NodeId{static_cast<node_id_wire_t>(pair >> 32)});
                    }
                },
                [&](ExtView e) { is_valid_offset(e.child()); },
                [&](AccountLeafView a) { is_valid_offset(a.storage()); },
                [](auto) {}});

        match(
            node,
            Cases{
                [](NullView) {},
                [](DigestView) {},
                [&](auto) {
                    node_rlp_span const rem = encode_rlp<true>(
                        node, node_rlp_span{rlp_buf}); // priming pass
                    // Only hash-referenced nodes (canonical RLP >= 32 B)
                    // are cached; smaller nodes are inlined by their
                    // parent, so caching their hash would make child_ref
                    // emit a 32-byte ref where the trie inlines it.
                    if (rem.rlp_size() >= 32) {
                        bytes32_t h;
                        monad_keccak256(
                            rem.rlp_data(), rem.rlp_size(), h.bytes);
                        hashes_.emplace(NodeId{node_offset}, h);
                    }
                }});

        set_offset_value<true>(node_offsets, node_offset);
        node = NodeViewBase{base + next_offset};
        node_offset = next_offset;
    }
    MONAD_ASSERT(node.bytes() == region_end); // nodes tile exactly
    is_valid_offset(root);

    // Every node was claimed exactly once, a leftover bit is a node not
    // reachable from root.
    MONAD_ASSERT(std::ranges::all_of(
        node_offsets, [](uint64_t const w) { return w == 0; }));
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
                    // Unreachable as written: the only EMPTY-tagged byte is
                    // the magic header at NULL_ID, id is non-null inside the
                    // loop, and the constructor checks every child offset is a
                    // recorded node start. That last premise is the fragile
                    // one — it lives in a different function, it is the most
                    // expensive thing the constructor does, and an optimisation
                    // that drops it turns this arm from diagnosed into
                    // undefined. The abort is one cold switch arm; keep it.
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
                MONAD_ASSERT(rem.rlp_size() >= 32);
                bytes32_t h;
                // RLP occupies the tail: [rem.end(), buf_end).
                monad_keccak256(rem.rlp_data(), rem.rlp_size(), h.bytes);

                hashes_.emplace(id, h);
                return h;
            }});
}

bytes32_t OffsetTrie::state_root()
{
    return hash(root);
}

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
    // A pre-state (blob) node this large is hash-referenced, so prime()
    // cached it bottom-up before any parent could reference it. Reaching
    // here on a cache miss means the parent held a forward/garbage offset.
    if constexpr (priming_pass) {
        MONAD_ABORT("offset trie: unprimed hash-referenced node (bad offset)");
    }
    bytes32_t h;
    monad_keccak256(child_rlp, child_rlp_len, h.bytes);
    hashes_.emplace(id, h);
    rlp::encode_string(dest.last(33), byte_string_view{h.bytes, 32});
    return dest.shrink(33);
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
    return match(
        node,
        Cases{
            [&, wrap](BranchView b) -> node_rlp_span {
                dest.back() = 0x80; // empty branch value — last list element
                dest = dest.shrink(1);
                std::array<node_id_wire_t, 16> const children = b.children();

                // A digest is pre-state only, put_node never shadows a digest
                // id and its original bytes are still its current bytes which
                // is why we can memcpy from the blob_ directly below.
                auto const digest_at = [this](node_id_wire_t const w) {
                    return w != 0 && w < OVERLAY_BASE &&
                           get_original(NodeId{w}).tag() == Tag::DIGEST;
                };

                auto const consecutive_digest = [](node_id_wire_t const a,
                                                   node_id_wire_t const b) {
                    return uint64_t{a} + HASH_RLP_LEN == uint64_t{b};
                };

                for (int i = 15; i >= 0; --i) {
                    if (!digest_at(children[static_cast<size_t>(i)])) {
                        dest = child_ref<priming_pass>(
                            NodeId{children[static_cast<size_t>(i)]}, dest);
                        continue;
                    }
                    // copy any contiguous digests directly into dest, since a
                    // digest node is already a valid RLP string
                    static_assert(DIGEST == 0x80 + KECCAK256_SIZE);
                    int lo = i;
                    while (lo > 0 &&
                           consecutive_digest(
                               children[static_cast<size_t>(lo - 1)],
                               children[static_cast<size_t>(lo)]) &&
                           digest_at(children[static_cast<size_t>(lo - 1)])) {
                        --lo;
                    }
                    size_t const digests_length =
                        static_cast<size_t>(i - lo + 1) * HASH_RLP_LEN;

                    unsigned char *const digests =
                        dest.last(digests_length).data();
                    std::memcpy(
                        digests,
                        blob_.data() + children[static_cast<size_t>(lo)],
                        digests_length);

                    dest = dest.shrink(digests_length);
                    i = lo;
                }
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
                dest.back() = 0xB8;
                dest = dest.shrink(1);
                dest = encode_path(dest, l.path(), /*terminating=*/true);
                return wrap(dest);
            },
            [&, encode_path, wrap](StorageLeafView l) -> node_rlp_span {
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
    out.append(rlp::encode_unsigned(acct.nonce));
    out.append(rlp::encode_unsigned(acct.balance));
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
    next_id_ = NodeId{static_cast<uint64_t>(next_id_) + 1};
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

std::pair<NodeId, Nibbles>
OffsetTrie::upsert_node(NodeId const id, NibblesView const key)
{
    hashes_.erase(id); // dirtied along the descent
    // Leaf split/overwrite, shared by both leaf types. Only re-emitting if the
    // displaced old leaf differs (`reput_old`): a storage leaf keeps its
    // value, an account leaf its fields and storage edge. `reput_old` runs
    // ahead of every other put_* here, which is what lets it still read the
    // displaced leaf's bytes.
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
                return split_leaf(l.path(), [&, l](NibblesView const np) {
                    return clone_acct(NULL_ID, l, np);
                });
            },
            [&](ExtView e) -> std::pair<NodeId, Nibbles> {
                Nibbles const p{e.path()};
                NibblesView const path{p};
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
                return {leaf, Nibbles{key.substr(cp + 1)}};
            },
            [&](BranchView b) -> std::pair<NodeId, Nibbles> {
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
                hashes_.erase(id);
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
