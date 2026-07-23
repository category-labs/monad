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
#include <category/core/keccak.hpp>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

#include <array>
#include <cstdint>
#include <cstring>
#include <optional>
#include <span>
#include <type_traits>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace mpt_witness
{
    // ── Format constants (see §3/§4) ────────────────────────────────────────
    enum Tag : uint8_t
    {
        BRANCH = 0,
        EXT = 1,
        LEAF_ACCT = 2,
        LEAF_STORAGE = 3,
        DIGEST = 4,
    };

    inline constexpr uint32_t HEADER_LEN = 8; // magic(4) root_off(4)
    // Splits the NodeId space by the high bit: blob offsets live below it,
    // fresh overlay ids at/above it. The TrieStore constructor rejects blobs
    // larger than this, so a blob offset can never reach the overlay half (no
    // collision). Real witnesses are ~MBs, far under 2 GiB.
    inline constexpr uint32_t OVERLAY_BASE = 1u << 31;

    // Upper bound on a single node's canonical RLP: 16 child refs (<=33 B each)
    // + value slot + list header. 700 leaves margin (matches partial_trie_db).
    inline constexpr size_t MAX_NODE_RLP = 700;

    // A node's stable identity (see §9). 0 = null; [HEADER_LEN, blob_len) is a
    // blob offset (unless shadowed by the overlay); >= OVERLAY_BASE is a fresh
    // overlay node.
    enum class NodeId : uint32_t
    {
    };
    inline constexpr NodeId NULL_ID{0};

    inline bool is_overlay_id(NodeId id)
    {
        return static_cast<uint32_t>(id) >= OVERLAY_BASE;
    }

    // Hasher so the overlay/hash maps can key on NodeId directly (an enum class
    // has no default ankerl/std hash). Delegates to the u32 hasher.
    struct NodeIdHash
    {
        using is_avalanching = void;

        uint64_t operator()(NodeId const id) const noexcept
        {
            return ankerl::unordered_dense::hash<uint32_t>{}(
                static_cast<uint32_t>(id));
        }
    };

    // ── little-endian unaligned scalar reads ────────────────────────────────
    inline uint32_t rd_u32(unsigned char const *const p)
    {
        uint32_t v;
        std::memcpy(&v, p, 4);
        return v; // rv64im is little-endian
    }

    inline uint16_t rd_u16(unsigned char const *const p)
    {
        uint16_t v;
        std::memcpy(&v, p, 2);
        return v;
    }

    // ── node writers ────────────────────────────────────────────────────────
    // Append one node's bytes to `out`. Children are referenced by NodeId, so a
    // producer passes blob offsets and the overlay passes overlay ids.
    void
    append_branch(byte_string &out, std::array<NodeId, 16> const &children);
    void append_ext(byte_string &out, mpt::NibblesView path, NodeId child);
    void
    append_storage(byte_string &out, mpt::NibblesView path, bytes32_t const &);
    void append_acct_raw(
        byte_string &out, mpt::NibblesView path, byte_string_view acct_rlp,
        NodeId storage);
    // No put_digest counterpart: mutation never creates a Digest, they only
    // ever arrive in the pre-state blob from the producer.
    void append_digest(byte_string &out, bytes32_t const &hash);

    // ── views ───────────────────────────────────────────────────────────────
    // NodeViewBase is the untyped view (a pointer at the node's tag byte).
    // Typed views derive from it and add only their tag's getters. Field
    // offsets per §4; scalars LE, hashes/value raw, account stored as RLP.
    class NodeViewBase
    {
    protected:
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

        unsigned char const *bytes() const
        {
            return p_;
        }

        // One past the last byte of this node, from its tag's fixed layout.
        // Aborts if the tag is invalid. Reads the node's length fields, so the
        // caller must bound the returned pointer against the region end (a
        // malformed blob can make it point past the buffer).
        unsigned char const *end() const;
    };

    // path nibbles live at p_+2 for EXT / LEAF_* tags: length prefix is one
    // byte at p_+1, packed nibbles follow.
    inline unsigned path_nlen(unsigned char const *const p)
    {
        return p[1];
    }

    inline unsigned path_bytes(unsigned char const *const p)
    {
        return (path_nlen(p) + 1) / 2;
    }

    inline mpt::NibblesView path_view(unsigned char const *const p)
    {
        return mpt::NibblesView{0u, path_nlen(p), p + 2};
    }

    inline byte_string_view byte_string_path_view(unsigned char const *const p)
    {
        return byte_string_view{p + 2, path_bytes(p)};
    }

    inline unsigned char const *NodeViewBase::end() const
    {
        switch (tag()) {
        case BRANCH: // tag + 16 child offsets
            return p_ + 1 + 64;
        case EXT: // path + child offset
            return byte_string_path_view(p_).end() + 4;
        case LEAF_ACCT: { // path + acc_len(u16) + acct_rlp + storage offset
            unsigned char const *const acc_len_p =
                byte_string_path_view(p_).end();
            return acc_len_p + 2 + rd_u16(acc_len_p) + 4;
        }
        case LEAF_STORAGE: // path + 32-byte value
            return byte_string_path_view(p_).end() + 32;
        case DIGEST: // tag + 32-byte hash
            return p_ + 1 + 32;
        }
        MONAD_ABORT("offset trie: invalid node tag");
    }

    class BranchView : public NodeViewBase
    {
    public:
        explicit BranchView(NodeViewBase b)
            : NodeViewBase(b)
        {
        }

        NodeId child(unsigned const i) const // NULL_ID if empty
        {
            return NodeId{rd_u32(p_ + 1 + 4 * i)};
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

        mpt::NibblesView path() const
        {
            return path_view(p_);
        }

        NodeId child() const
        {
            return NodeId{rd_u32(byte_string_path_view(p_).end())};
        }
    };

    class AcctLeafView : public NodeViewBase
    {
    public:
        explicit AcctLeafView(NodeViewBase b)
            : NodeViewBase(b)
        {
        }

        mpt::NibblesView path() const
        {
            return path_view(p_);
        }

        // stored Ethereum account RLP (for hashing / decode)
        byte_string_view account_rlp() const
        {
            unsigned char const *const acc_len_p =
                byte_string_path_view(p_).end();
            unsigned const acc_len = rd_u16(acc_len_p);
            return byte_string_view{acc_len_p + 2, acc_len};
        }

        // lazily RLP-decode the account (fields for read_account)
        Account account() const
        {
            byte_string_view enc = account_rlp();
            bytes32_t
                storage_root; // discarded; storage is traversed via storage()
            auto res = rlp::decode_account(storage_root, enc);
            MONAD_ASSERT(res.has_value());
            return res.value();
        }

        NodeId storage() const // NULL_ID if no storage subtree materialized
        {
            return NodeId{rd_u32(account_rlp().end())};
        }
    };

    class StorageLeafView : public NodeViewBase
    {
    public:
        explicit StorageLeafView(NodeViewBase b)
            : NodeViewBase(b)
        {
        }

        mpt::NibblesView path() const
        {
            return path_view(p_);
        }

        bytes32_t value() const
        {
            bytes32_t v;
            std::memcpy(v.bytes, byte_string_path_view(p_).end(), 32);
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
            std::memcpy(h.bytes, p_ + 1, 32);
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
            return v(AcctLeafView{n});
        case LEAF_STORAGE:
            return v(StorageLeafView{n});
        case DIGEST:
            return v(DigestView{n});
        }
        MONAD_ABORT("bad node tag");
    }

    // ── TrieStore — immutable blob + stable-id overlay ───────────────────────
    class TrieStore
    {
    public:
        // Wrap the read-only node blob, structurally validate it, and prime the
        // hash cache (see prime()). Aborts if the blob is malformed.
        explicit TrieStore(byte_string_view blob);

        // account-trie root, fixed at construction: upsert_node and
        // erase_node keep this id stable, so it is the permanent handle to the
        // account trie. An empty trie gets a fresh overlay-id sentinel.
        NodeId const root;

        NodeViewBase get_original(NodeId const id) const
        {
            MONAD_ASSERT(!is_overlay_id(id) && id != NULL_ID);
            MONAD_ASSERT(
                static_cast<uint32_t>(id) >= HEADER_LEN &&
                static_cast<uint32_t>(id) < blob_.size());
            return NodeViewBase{blob_.data() + static_cast<uint32_t>(id)};
        }

        // Current bytes for `id` — overlay entry if present, else the blob.
        NodeViewBase get_current(NodeId const id) const
        {
            auto const it = overlay_.find(id);
            if (it != overlay_.end()) {
                return NodeViewBase{it->second.data()};
            }
            return get_original(id);
        }

        bool exists(NodeId const id) const
        {
            if (id == NULL_ID) {
                return false;
            }
            if (is_overlay_id(id) && overlay_.find(id) == overlay_.end()) {
                return false;
            }
            return true;
        }

        // Walk the (pre-state) trie rooted at `id` following `key`; return the
        // leaf view if the key is present, else nullopt. Aborts on a Digest
        // (incomplete witness). Traverses through the view accessors via match.
        std::optional<NodeViewBase>
        find_original(NodeId id, mpt::NibblesView key) const;

        // ── mutation + hashing — declared, not yet implemented (see §13) ─────
        NodeId put_branch(NodeId, std::array<NodeId, 16> const &);
        NodeId put_ext(NodeId, mpt::NibblesView, NodeId);
        NodeId put_storage(NodeId, mpt::NibblesView, bytes32_t const &);
        NodeId put_acct(
            NodeId, mpt::NibblesView, Account const &, bytes32_t const &,
            NodeId);
        std::pair<NodeId, mpt::Nibbles>
        upsert_node(NodeId const id, mpt::NibblesView const key);

        enum class EraseResult
        {
            Erased,
            Unmodified,
            SameShape,
            NewShape
        };
        EraseResult erase_node(NodeId, mpt::NibblesView);

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
        // Constructed from a std::span, so it slices/round-trips through the
        // std::span-typed child_ref/encode_rlp signatures.
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

        // The node's full canonical Ethereum RLP. Reads `node`'s fields and
        // resolves its children through child_ref.
        template <bool priming_pass = false>
        node_rlp_span encode_rlp(NodeViewBase node, node_rlp_span dest);

        // Cache the hash of one blob node whose children are already primed.
        // Mirrors child_ref's rule: only hash-referenced nodes (RLP >= 32 B)
        // and Digests are cached; sub-32-B nodes are inlined by their parent.
        void prime_node(NodeViewBase id);

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
            NodeId const parent, mpt::NibblesView const prefix,
            NodeViewBase const child);

        // Like put_acct but takes the account's already-encoded RLP verbatim,
        // preserving the stored storage_root exactly (used when re-pathing an
        // account leaf on collapse/merge, where re-deriving it is impossible).
        NodeId put_acct_raw(
            NodeId id, mpt::NibblesView path, byte_string_view acct_rlp,
            NodeId storage);

        // Account-trie recursion behind upsert_account / erase_account —
        // mirrors upsert_storage / erase_storage but over account leaves.
        // upsert reports the found/created leaf id via `leaf` so commit can
        // fill in its fields.
        NodeId
        upsert_account_node(NodeId id, mpt::NibblesView key, NodeId &leaf);
        NodeId erase_account_node(NodeId id, mpt::NibblesView key);

        // Initial root id from the blob header (root_off, or an overlay-id
        // sentinel for an empty trie); also validates the header.
        static NodeId read_root(byte_string_view blob);

        byte_string_view blob_;
        ankerl::unordered_dense::map<NodeId, byte_string, NodeIdHash> overlay_;
        ankerl::unordered_dense::map<NodeId, bytes32_t, NodeIdHash> hashes_;
        NodeId next_id_{OVERLAY_BASE}; // fresh-id counter (>= OVERLAY_BASE)
    };

    using CodeIndex =
        ankerl::unordered_dense::map<bytes32_t, vm::SharedIntercode>;

} // namespace mpt_witness

// ── OffsetTrieDb — Db over the offset-format trie ───────────────────────────
// Coexists with PartialTrieDb; reads are implemented, writes/roots are stubbed
// (land with TrieStore mutation + hashing).
class OffsetTrieDb final : public Db
{
    mpt_witness::TrieStore store_;
    mpt_witness::CodeIndex codes_;
    uint64_t block_number_{0};
    BlockHeader last_committed_header_{};

public:
    OffsetTrieDb(mpt_witness::TrieStore store, mpt_witness::CodeIndex codes)
        : store_(std::move(store))
        , codes_(std::move(codes))
    {
    }

    bool is_page_encoded() const override
    {
        return false;
    }

    std::optional<Account> read_account(Address const &addr) override;

    bytes32_t read_storage(
        Address const &addr, Incarnation, bytes32_t const &slot) override;

    vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        auto const it = codes_.find(code_hash);
        return it == codes_.end() ? vm::make_shared_intercode({}) : it->second;
    }

    storage_page_t
    read_storage_page(Address const &, Incarnation, bytes32_t const &) override
    {
        MONAD_ABORT("OffsetTrieDb: read_storage_page unsupported");
    }

    BlockHeader read_eth_header() override
    {
        return last_committed_header_;
    }

    bytes32_t state_root() override
    {
        return store_.state_root();
    }

    bytes32_t receipts_root() override
    {
        return last_committed_header_.receipts_root;
    }

    bytes32_t transactions_root() override
    {
        return last_committed_header_.transactions_root;
    }

    std::optional<bytes32_t> withdrawals_root() override
    {
        return last_committed_header_.withdrawals_root;
    }

    uint64_t get_block_number() const override
    {
        return block_number_;
    }

    void set_block_and_prefix(
        uint64_t const block_number, bytes32_t const &) override
    {
        block_number_ = block_number;
    }

    void commit(
        bytes32_t const &block_id, CommitBuilder &builder,
        BlockHeader const &header, StateDeltas const &state_deltas,
        std::function<void(BlockHeader &)> populate_header_fn) override;

    void finalize(uint64_t, bytes32_t const &) override {}

    void update_verified_block(uint64_t) override {}

    void update_voted_metadata(uint64_t, bytes32_t const &) override {}

    void update_proposed_metadata(uint64_t, bytes32_t const &) override {}
};

MONAD_NAMESPACE_END
