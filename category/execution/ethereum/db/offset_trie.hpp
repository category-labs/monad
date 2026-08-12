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
#include <category/core/bit_primitives.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <ankerl/unordered_dense.h>

#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <span>
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

// Upper bound on a single node's canonical RLP: 16 child refs (<=33 B each)
// + value slot + list header. 700 leaves margin.
inline constexpr size_t MAX_NODE_RLP = 700;

// A node's stable id. 0 = null; `n` in the [HEADER_LEN, blob_len) range is
// a blob offset (unless shadowed by an overlay); n >= OVERLAY_BASE is a
// fresh overlay node.
//
// The id is register-width, independent of the 32-bit child field the wire
// format stores it in (node_id_wire below)
enum class NodeId : uint64_t
{
};
inline constexpr NodeId NULL_ID{0};

// Width of a child/root field in the node encoding
using node_id_wire = uint32_t;

inline constexpr size_t HASH_RLP_LEN = 33; // 0xa0 ‖ 32 B
// Widest that run can get: 1 + 8 for the nonce, 1 + 32 for the balance. Both
// are RLP-zeroless, so real accounts sit far below this.
inline constexpr size_t MAX_NONCE_BALANCE_RLP_LEN = 42;

// Splits the NodeId space by the wire field's high bit: blob offsets live
// below it, fresh overlay ids at/above it. The OffsetTrie constructor rejects
// blobs larger than this, so a blob offset can never reach the overlay half
// (no collision). Real witnesses are ~MBs, far under 2 GiB.
inline constexpr uint64_t OVERLAY_BASE = uint64_t{1} << 31;

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

// Widen a wire child field to an id. The one place the two representations
// meet on the read side (append_node_id is its write-side counterpart).
inline NodeId read_node_id(unsigned char const *const p)
{
    static_assert(std::endian::native == std::endian::little);
    node_id_wire v;
    std::memcpy(&v, p, sizeof(v));
    return NodeId{v};
}

// ── node writers ─────────────────────────────────────────────────────────────
void append_branch(byte_string &out, std::array<NodeId, 16> const &children);
void append_ext(byte_string &out, NibblesView path, NodeId child);
void append_storage(byte_string &out, NibblesView path, bytes32_t const &);
void append_acct(
    byte_string &out, NodeId storage, Account const &, NibblesView path);
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
    return p + sizeof(node_id_wire);
}

// One past a LEAF_ACCT's field runs, from the start of its code hash: the
// fixed-width hash, then the length byte and the nonce ‖ balance run it
// counts.
inline unsigned char const *rlp_end(unsigned char const *const p)
{
    return p + HASH_RLP_LEN + 1 + p[HASH_RLP_LEN];
}

inline unsigned char const *NodeViewBase::end() const
{
    switch (tag()) {
    case BRANCH: // 16 child offsets
        return payload() + 16 * sizeof(node_id_wire);
    case EXT: // child offset + path
        return path_view_end(child_end(payload()));
    case LEAF_ACCT: // storage offset + code hash + nonce & balance length +
                    // nonce & balance + path
        return path_view_end(rlp_end(child_end(payload())));
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
        return read_node_id(payload() + sizeof(node_id_wire) * i);
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
        return read_node_id(payload());
    }
};

// An account leaf stores the account's fields in the following order:
// - storage node id
// - code hash RLP
// - nonce ‖ balance RLP
// - nibble path length
// - nibble path
class AccountLeafView : public NodeViewBase
{
public:
    explicit AccountLeafView(NodeViewBase b)
        : NodeViewBase(b)
    {
    }

    // NULL_ID if no storage subtree materialized.
    NodeId storage() const
    {
        return read_node_id(payload());
    }

    // code_hash as an RLP string
    byte_string_view code_hash_rlp() const
    {
        return byte_string_view{child_end(payload()), HASH_RLP_LEN};
    }

    // nonce ‖ balance as RLP strings
    byte_string_view nonce_balance_rlp() const
    {
        unsigned char const *const len_p = child_end(payload()) + HASH_RLP_LEN;
        size_t const len = len_p[0];
        MONAD_ASSERT(len >= 2 && len <= MAX_NONCE_BALANCE_RLP_LEN);
        return byte_string_view{len_p + 1, len};
    }

    NibblesView path() const
    {
        return path_view(rlp_end(child_end(payload())));
    }

    // lazily RLP-decode the account (fields for read_account)
    Account account() const
    {
        Account acct;
        // Decoded through the accessors, so the stored length is bounded here
        // as well and not only on the extent walk.
        byte_string_view code_hash = code_hash_rlp();
        auto const hash = rlp::decode_bytes32(code_hash);
        MONAD_ASSERT(hash.has_value());
        acct.code_hash = hash.value();
        byte_string_view nonce_balance = nonce_balance_rlp();
        auto const nonce = rlp::decode_unsigned<uint64_t>(nonce_balance);
        MONAD_ASSERT(nonce.has_value());
        acct.nonce = nonce.value();
        auto const balance = rlp::decode_unsigned<uint256_t>(nonce_balance);
        MONAD_ASSERT(balance.has_value());
        acct.balance = balance.value();
        MONAD_ASSERT(nonce_balance.empty());
        return acct;
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

    byte_string_view hash_view() const
    {
        return byte_string_view{payload(), 32};
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
    byte_string_view blob_;
    ankerl::unordered_dense::map<NodeId, byte_string, NodeIdHash> overlay_{};
    ankerl::unordered_dense::map<NodeId, bytes32_t, NodeIdHash> hashes_{};
    NodeId next_id_{OVERLAY_BASE}; // fresh-id counter (>= OVERLAY_BASE)
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
    NodeId put_acct(NodeId, NibblesView, Account const &, NodeId);
    // Copies account data verbatim but appends a new path
    NodeId clone_acct(NodeId id, AccountLeafView acc, NibblesView new_path);
    std::pair<NodeId, Nibbles>
    upsert_node(NodeId const id, NibblesView const key);

    // What the node at the erased key's ancestor has to do about it. There is
    // no shape dimension here on purpose: an id outlives a re-encode, so a
    // parent never learns (or needs to learn) whether a surviving child stayed
    // an extension or collapsed into a leaf — that stability is what keeps the
    // rewrite from bubbling up.
    enum class EraseResult
    {
        Erased,
        Unmodified,
        Modified
    };
    EraseResult erase_node(NodeId, NibblesView);

    // keccak of the (current) trie rooted at `id`; NULL_ID -> NULL_ROOT.
    // Serves the account root and the storage sub-root an account leaf spans.
    // Consults hashes_; recomputes + caches a missing id.
    //
    // `id` must be a trie root. Unlike the priming pass this caches whatever
    // it is given, and child_ref consults hashes_ before deciding whether to
    // inline, so a cached id whose canonical RLP is under 32 B would be
    // hash-referenced by its parent where the trie inlines it. Roots are
    // exempt because they are never inlined — and both call sites hand over a
    // node that spells a whole 64-nibble key, or a branch, so is over 32 B
    // anyway.
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
    // rv32 (SP1) writes the 33-byte hash-ref inline instead of through
    // rlp::encode_string, whose generic path is a memcpy CALL per child.
    // ZisK deliberately keeps encode_string: measured -6.2 % with the inline
    // copy there, because its memcpy handles misalignment better than a
    // generic shift-combine. Guarded, so only the backend that wins uses it.
    static inline node_rlp_span
    write_hash_ref(node_rlp_span dest, unsigned char const *const hash32)
    {
#if defined(MONAD_ZKVM_SP1)
        auto const span33 = dest.last(33);
        span33.data()[0] = 0xa0;
        bits::copy32_from_aligned(span33.data() + 1, hash32);
#else
        rlp::encode_string(dest.last(33), byte_string_view{hash32, 32});
#endif
        return dest.shrink(33);
    }

    node_rlp_span child_ref_compute(
        NodeId const id, NodeViewBase const node, node_rlp_span dest);

    template <bool priming_pass>
    inline node_rlp_span child_ref(NodeId const id, node_rlp_span dest)
    {
        if (id == NULL_ID) {
            dest.back() = 0x80; // RLP empty string
            return dest.shrink(1);
        }
        // Pre-state (priming) reads bound-check and resolve against the blob;
        // current reads consult the overlay first.
        NodeViewBase const node = [&]() -> NodeViewBase {
            if constexpr (priming_pass) {
                return get_original(id);
            }
            else {
                return get_current(id);
            }
        }();
        return match(
            node,
            Cases{
                [](NullView) -> node_rlp_span {
                    MONAD_ABORT("malformed trie: node not found");
                },
                [&](DigestView d) {
                    return write_hash_ref(dest, d.hash_view().data());
                },
                [&](auto) {
                    if (auto const it = hashes_.find(id); it != hashes_.end()) {
                        return write_hash_ref(dest, it->second.bytes);
                    }
                    return child_ref_compute<priming_pass>(id, node, dest);
                }});
    }

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

    // Fold `prefix` onto `child`'s path when `child` is a leaf/ext, committing
    // the merged node under `parent`'s id so nothing above is repointed. The
    // trie's collapse/merge primitive. A branch `child` is left alone — a path
    // can't fold into one — and neither caller needs it to be: the extension
    // caller's node already spells `prefix`, and the branch-collapse caller
    // wraps a branch child in a one-nibble extension itself.
    void fold_ext_node_path_maybe(
        NodeId const parent, NibblesView const prefix,
        NodeViewBase const child);

    // Initial root id from the blob header (root_offset, or an overlay-id
    // sentinel for an empty trie); also validates the header.
    static NodeId read_root(byte_string_view blob);
};

MONAD_MPT_NAMESPACE_END
