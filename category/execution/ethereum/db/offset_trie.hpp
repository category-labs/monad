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

#pragma once

// Offset-based, zero-copy witness trie for the zkVM guest.

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <ankerl/unordered_dense.h>

#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <span>
#include <vector>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

enum Tag : uint8_t
{
    BRANCH = 0,
    EXT = 1,
    LEAF_ACCT = 2,
    LEAF_STORAGE = 3,
    DIGEST = 4,
    // NULL_ID addresses the blob's first magic byte, so the magic's leading
    // 'M' doubles as the null node's tag: a null child dereferences to a
    // real view instead of needing a null pre-check at every call site.
    // read_root asserts the magic, which is what guarantees the byte is
    // there.
    EMPTY = 'M',
};

inline constexpr uint32_t HEADER_LEN = 8; // magic(4) root_offset(4)
// Splits the NodeId space by the high bit: blob offsets live below it,
// fresh overlay ids at/above it. The OffsetTrie constructor rejects blobs
// larger than this, so a blob offset can never reach the overlay half (no
// collision). Real witnesses are ~MBs, far under 2 GiB.
inline constexpr uint32_t OVERLAY_BASE = 1u << 31;

// The on-blob encoding of a node id is FOUR bytes, independent of the width of
// the in-memory type. Keeping the two apart is what lets NodeId be 64-bit in
// registers -- which kills the addw/addiw/srliw class in the reader's hottest
// paths -- while the witness format stays exactly as generated. Deriving node
// extents from sizeof(NodeId) instead couples them: widening the enum then
// makes end() believe a branch is 128 bytes rather than 64, and the reader
// misparses the blob it was handed.
inline constexpr size_t NODE_ID_WIRE = 4;

// Upper bound on a single node's canonical RLP: 16 child refs (<=33 B each)
// + value slot + list header. 700 leaves margin.
inline constexpr size_t MAX_NODE_RLP = 700;

// A node's stable id. 0 = null; `n` in the [HEADER_LEN, blob_len) range is
// a blob offset (unless shadowed by an overlay); n >= OVERLAY_BASE is a
// fresh overlay node.
// 64-bit on purpose: see NODE_ID_WIRE above -- the register width and the wire
// width are deliberately different.
enum class NodeId : uint64_t
{
};
inline constexpr NodeId NULL_ID{0};

inline bool is_overlay_id(NodeId id)
{
    return static_cast<uint64_t>(id) >= OVERLAY_BASE;
}

struct NodeIdHash
{
    using is_avalanching = void;

    uint64_t operator()(NodeId const id) const noexcept
    {
        return ankerl::unordered_dense::hash<uint64_t>{}(
            static_cast<uint64_t>(id));
    }
};

// ── little-endian unaligned scalar reads ─────────────────────────────────────
inline uint32_t read_u32(unsigned char const *const p)
{
    static_assert(std::endian::native == std::endian::little);
    uint32_t v;
    std::memcpy(&v, p, 4);
    return v;
}

inline uint16_t read_u16(unsigned char const *const p)
{
    static_assert(std::endian::native == std::endian::little);
    uint16_t v;
    std::memcpy(&v, p, 2);
    return v;
}

// ── node writers ─────────────────────────────────────────────────────────────
void append_branch(byte_string &out, std::array<NodeId, 16> const &children);
void append_ext(byte_string &out, NibblesView path, NodeId child);
void append_storage(byte_string &out, NibblesView path, bytes32_t const &);
void append_acct_raw(
    byte_string &out, NibblesView path, byte_string_view acct_rlp,
    NodeId storage);
// No put_digest counterpart: mutation never creates a Digest, they only
// ever arrive in the pre-state blob from the producer.
void append_digest(byte_string &out, bytes32_t const &hash);

// ── views ────────────────────────────────────────────────────────────────────
// NodeViewBase is the untyped view (a pointer at the node's tag byte).
// Typed views derive from it and add only their tag's getters.
class NodeViewBase
{
    unsigned char const *p_;

public:
    explicit NodeViewBase(unsigned char const *const p)
        : p_(p)
    {
    }

    Tag tag() const
    {
        return Tag(*p_);
    }

    inline unsigned char const *bytes() const
    {
        return p_;
    }

    inline unsigned char const *payload() const
    {
        return p_ + 1;
    }

    // One past the last byte of this node, from its tag's fixed layout.
    // Aborts if the tag is invalid. Reads the node's length fields, so the
    // caller must bound the returned pointer against the region end (a
    // malformed blob can make it point past the buffer).
    unsigned char const *end() const;
};

// Nibble count
inline unsigned path_length(unsigned char const *const p)
{
    return p[0];
}

// Packed size of the path in bytes — half the nibble count, rounded up.
inline unsigned path_byte_length(unsigned char const *const p)
{
    return (path_length(p) + 1) / 2;
}

inline NibblesView path_view(unsigned char const *const p)
{
    return NibblesView{0u, path_length(p), p + 1};
}

inline unsigned char const *path_view_end(unsigned char const *const p)
{
    return p + 1 + path_byte_length(p);
}

// LEAF_ACCT and EXT keep their child id at a fixed position right after the
// tag, so storage()/child() is a constant-offset read instead of a walk
// over a path or account RLP. The rest of the node follows that field.
inline unsigned char const *child_end(unsigned char const *const p)
{
    return p + NODE_ID_WIRE;
}

inline unsigned char const *account_rlp_end(unsigned char const *const p)
{
    uint16_t const rlp_len = read_u16(p);
    return p + sizeof(rlp_len) + rlp_len;
}

inline unsigned char const *NodeViewBase::end() const
{
    switch (tag()) {
    case BRANCH: // 16 child offsets
        return payload() + 16 * NODE_ID_WIRE;
    case EXT: // child offset + path
        return path_view_end(child_end(payload()));
    case LEAF_ACCT: // storage offset + path + acc length + acc rlp
        return account_rlp_end(path_view_end(child_end(payload())));
    case LEAF_STORAGE: // 32-byte value + path
        return path_view_end(payload() + 32);
    case DIGEST: // 32-byte hash
        return payload() + 32;
    case EMPTY: // pointing at the header
        return bytes() + HEADER_LEN;
    }
    MONAD_ABORT("offset trie: invalid node tag");
}

class NullView : public NodeViewBase
{
public:
    explicit NullView(NodeViewBase b)
        : NodeViewBase(b)
    {
    }
};

class BranchView : public NodeViewBase
{
public:
    explicit BranchView(NodeViewBase b)
        : NodeViewBase(b)
    {
    }

    NodeId child(unsigned const i) const // NULL_ID if empty
    {
        return NodeId{read_u32(payload() + 4 * i)};
    }

    std::array<NodeId, 16> children() const
    {
        std::array<NodeId, 16> out{};
        for (unsigned i = 0; i < 16; ++i) {
            out[i] = child(i);
        }
        return out;
    }
};

class ExtView : public NodeViewBase
{
public:
    explicit ExtView(NodeViewBase b)
        : NodeViewBase(b)
    {
    }

    NibblesView path() const
    {
        return path_view(child_end(payload()));
    }

    NodeId child() const
    {
        return NodeId{read_u32(payload())};
    }
};

class AccountLeafView : public NodeViewBase
{
public:
    explicit AccountLeafView(NodeViewBase b)
        : NodeViewBase(b)
    {
    }

    NibblesView path() const
    {
        return path_view(child_end(payload()));
    }

    // stored Ethereum account RLP (for hashing / decode)
    byte_string_view account_rlp() const
    {
        unsigned char const *const acc_len_p =
            path_view_end(child_end(payload()));
        unsigned const acc_len = read_u16(acc_len_p);
        return byte_string_view{acc_len_p + 2, acc_len};
    }

    // lazily RLP-decode the account (fields for read_account)
    Account account() const
    {
        byte_string_view enc = account_rlp();
        bytes32_t storage_root; // discarded; storage is traversed via storage()
        auto res = rlp::decode_account(storage_root, enc);
        MONAD_ASSERT(res.has_value());
        return res.value();
    }

    // NULL_ID if no storage subtree materialized. Fixed offset — the whole
    // point of storing it ahead of the path and account RLP.
    NodeId storage() const
    {
        return NodeId{read_u32(payload())};
    }
};

class StorageLeafView : public NodeViewBase
{
public:
    explicit StorageLeafView(NodeViewBase b)
        : NodeViewBase(b)
    {
    }

    NibblesView path() const
    {
        return path_view(payload() + 32);
    }

    bytes32_t value() const
    {
        bytes32_t v;
        std::memcpy(v.bytes, payload(), 32);
        return v;
    }
};

class DigestView : public NodeViewBase
{
public:
    explicit DigestView(NodeViewBase b)
        : NodeViewBase(b)
    {
    }

    bytes32_t hash() const
    {
        bytes32_t h;
        std::memcpy(h.bytes, payload(), 32);
        return h;
    }
};

template <class... Fs>
decltype(auto) match(NodeViewBase n, Fs &&...fs)
{
    Cases const v{std::forward<Fs>(fs)...};
    switch (n.tag()) {
    case BRANCH:
        return v(BranchView{n});
    case EXT:
        return v(ExtView{n});
    case LEAF_ACCT:
        return v(AccountLeafView{n});
    case LEAF_STORAGE:
        return v(StorageLeafView{n});
    case DIGEST:
        return v(DigestView{n});
    case EMPTY:
        return v(NullView{n});
    }
    MONAD_ABORT("bad node tag");
}

// ── OffsetTrie — immutable blob + stable-id overlay ──────────────────────────
class OffsetTrie
{
public:
    // Wrap the read-only node blob, structurally validate it, and prime the
    // hash cache (see prime()). Aborts if the blob is malformed.
    explicit OffsetTrie(byte_string_view blob);

    // Account-trie root, NULL_ID while the trie is empty. upsert_node and
    // erase_node keep a materialised root's id stable, so a caller only
    // reassigns it across the empty/non-empty transitions — exactly as
    // PartialTrieDb::commit already threads a storage sub-root.
    NodeId root;

    NodeViewBase empty() const
    {
        // The blob is a node region, not text: NodeViewBase reads the tag
        // at this byte and takes every extent from the node layout, so
        // there is nothing to NUL-terminate.
        // NOLINTNEXTLINE(bugprone-suspicious-stringview-data-usage)
        return NodeViewBase{blob_.data()};
    }

    NodeViewBase get_original(NodeId const id) const
    {
        // NULL_ID resolves to the blob's first magic byte, i.e. the EMPTY
        // tag
        MONAD_ASSERT(
            id == NULL_ID || (static_cast<uint64_t>(id) >= HEADER_LEN &&
                              static_cast<uint64_t>(id) < blob_.size()));
        return NodeViewBase{blob_.data() + static_cast<uint64_t>(id)};
    }

    // Current bytes for `id` — overlay entry if present, else the blob.
    // put_node shadows a rewritten blob node under its own blob id, so the
    // overlay has to be consulted for every id, not just fresh ones. A
    // fresh id with no entry yet is a node upsert allocated but no put_*
    // has materialised: it reads as empty.
    NodeViewBase get_current(NodeId const id) const
    {
        auto const it = overlay_.find(id);
        if (it != overlay_.end()) {
            return NodeViewBase{it->second.data()};
        }
        return is_overlay_id(id) ? empty() : get_original(id);
    }

    // Walk the (pre-state) trie rooted at `id` following `key`; return the
    // leaf view if the key is present, else `NullView`. Aborts on a Digest
    // (incomplete witness). Traverses through the view accessors via match.
    NodeViewBase find_original(NodeId id, NibblesView key) const;

    NodeId put_branch(NodeId, std::array<NodeId, 16> const &);
    NodeId put_ext(NodeId, NibblesView, NodeId);
    NodeId put_storage(NodeId, NibblesView, bytes32_t const &);
    NodeId
    put_acct(NodeId, NibblesView, Account const &, bytes32_t const &, NodeId);
    std::pair<NodeId, Nibbles>
    upsert_node(NodeId const id, NibblesView const key);

    enum class EraseResult
    {
        Erased,
        Unmodified,
        SameShape,
        NewShape
    };
    EraseResult erase_node(NodeId, NibblesView);

    // keccak of the (current) trie rooted at `id`; NULL_ID -> NULL_ROOT.
    // Serves the account root and, at commit, freshly built storage
    // sub-roots. Consults hashes_; recomputes + caches a missing id.
    bytes32_t hash(NodeId id);
    bytes32_t state_root();

private:
    // A thin view over an RLP scratch buffer of fixed capacity
    // MAX_NODE_RLP. Encoding writes the payload into the *tail* of the
    // buffer, so `data()` always stays at the buffer start and `size()`
    // shrinks as bytes are written. The live RLP region is therefore
    // [data() + size(), buf_end):
    //   rlp_data() = data() + size(),  rlp_size() = MAX_NODE_RLP - size().
    struct node_rlp_span : std::span<unsigned char>
    {
        explicit node_rlp_span(std::span<unsigned char> const s)
            : std::span<unsigned char>(s)
        {
        }

        // The written RLP is the tail past size(), not a subspan of *this,
        // so rlp_data() needs the raw base pointer. Everyone else must
        // reach bytes through last(): hide the front pointer to stop
        // accidental writes to the unwritten head being mistaken for the
        // payload.
        unsigned char *data() const = delete;

        unsigned char const *rlp_data() const
        {
            return std::span<unsigned char>::data() + size();
        }

        size_t rlp_size() const
        {
            return MAX_NODE_RLP - size();
        }

        node_rlp_span shrink(size_t const n) const
        {
            return node_rlp_span{first(size() - n)};
        }
    };

    template <bool priming_pass>
    node_rlp_span child_ref(NodeId id, node_rlp_span dest);

    template <bool priming_pass>
    node_rlp_span child_ref_slow(NodeId id, node_rlp_span dest);

    // The node's full canonical Ethereum RLP. Reads `node`'s fields and
    // resolves its children through child_ref.
    template <bool priming_pass = false>
    node_rlp_span encode_rlp(NodeViewBase node, node_rlp_span dest);

    NodeId fresh_id();

    // Commit `node` bytes to the overlay under `id`, returning `id`. If
    // `id == NULL_ID` a fresh overlay id is allocated; otherwise the node's
    // bytes are replaced (shadowing the blob) and its stale hash dropped.
    // This is the single allocation/rewrite point behind every put_*.
    NodeId put_node(NodeId id, byte_string node);

    // Fold `prefix` onto `child`'s path when `child` is a leaf/ext,
    // committing the merged node under `child` (returned). Returns nullopt
    // when `child` is a branch — a path can't fold into one, so the caller
    // wraps it in an extension instead. The trie's collapse/merge
    // primitive.
    Tag fold_ext_node_path_maybe(
        NodeId const parent, NibblesView const prefix,
        NodeViewBase const child);

    // Like put_acct but takes the account's already-encoded RLP verbatim,
    // preserving the stored storage_root exactly (used when re-pathing an
    // account leaf on collapse/merge, where re-deriving it is impossible).
    NodeId put_acct_raw(
        NodeId id, NibblesView path, byte_string_view acct_rlp, NodeId storage);

    // Account-trie recursion behind upsert_account / erase_account —
    // mirrors upsert_storage / erase_storage but over account leaves.
    // upsert reports the found/created leaf id via `leaf` so commit can
    // fill in its fields.
    NodeId upsert_account_node(NodeId id, NibblesView key, NodeId &leaf);
    NodeId erase_account_node(NodeId id, NibblesView key);

    // Initial root id from the blob header (root_offset, or an overlay-id
    // sentinel for an empty trie); also validates the header.
    static NodeId read_root(byte_string_view blob);

    byte_string_view blob_;
    ankerl::unordered_dense::map<NodeId, byte_string, NodeIdHash> overlay_;
    // Hash cache, split by id space. Blob nodes (id < OVERLAY_BASE) live in a
    // FLAT table: node starts are >= 7 bytes apart (min node: EXT = tag +
    // 1-byte path prefix + 1 nibble byte + 4-byte child offset), so
    // offset >> 2 is collision-free and the lookup is one indexed load -- no
    // key hash, no probe, no rehash. Entry = index+1 into blob_hashes_, 0 =
    // not cached (digest, inlined-small, or dirtied). The map keeps only
    // overlay nodes and recomputed dirty originals.
    std::vector<bytes32_t> blob_hashes_;
    std::vector<uint32_t> blob_hash_idx_;

    bytes32_t const *blob_hash_find(NodeId const id) const noexcept
    {
        uint32_t const slot = blob_hash_idx_[static_cast<uint64_t>(id) >> 2];
        return slot ? &blob_hashes_[slot - 1] : nullptr;
    }

    void blob_hash_put(NodeId const id, bytes32_t const &h)
    {
        blob_hashes_.push_back(h);
        blob_hash_idx_[static_cast<uint64_t>(id) >> 2] =
            static_cast<uint32_t>(blob_hashes_.size());
    }

    void hash_cache_erase(NodeId const id)
    {
        if (!is_overlay_id(id)) {
            blob_hash_idx_[static_cast<uint64_t>(id) >> 2] = 0;
        }
        hashes_.erase(id);
    }

    ankerl::unordered_dense::map<NodeId, bytes32_t, NodeIdHash> hashes_;
    NodeId next_id_{OVERLAY_BASE}; // fresh-id counter (>= OVERLAY_BASE)
};

MONAD_MPT_NAMESPACE_END
