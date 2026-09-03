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
// The account leaf is decomposed, so reading a field decodes it here.
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
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
        // 0xa0 is RLP's prefix for a 32-byte string, so a digest node's blob
        // bytes -- tag | hash32 -- are already the hash-reference its parent
        // must emit. DIGEST_NODE_LEN was made equal to HASH_RLP_LEN so that a
        // run of digest children is the run of refs the parent needs; this
        // finishes that, and the consumer's stamp loop over the run goes away.
        DIGEST = 0xa0,
    };

    inline constexpr uint32_t HEADER_LEN = 8; // magic(4) root_off(4)
    // 0xa0 | 32 B: how a code hash sits in an account leaf.
    inline constexpr size_t HASH_RLP_LEN = 33;
    // nonce | balance sit behind a ONE-BYTE length, which caps that run:
    // RLP(uint64) is at most 9 B and RLP(uint256) at most 33 B.
    inline constexpr size_t MAX_NONCE_BALANCE_RLP_LEN = 42;
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


    // ── node writers ────────────────────────────────────────────────────────
    // Append one node's bytes to `out`. Children are referenced by NodeId, so a
    // producer passes blob offsets and the overlay passes overlay ids.
    void
    append_branch(byte_string &out, std::array<NodeId, 16> const &children);
    void append_ext(byte_string &out, mpt::NibblesView path, NodeId child);
    void
    append_storage(byte_string &out, mpt::NibblesView path, bytes32_t const &);
    void append_acct(
        byte_string &out, NodeId storage, Account const &acct,
        mpt::NibblesView path);
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

    // ── THE NODE LAYOUT, IN ONE PLACE ───────────────────────────────────────
    // tag(1), then a fixed-width run the tag decides, then the path for the tags
    // that carry one. fixed_end() is the ONLY function that knows where a run
    // ends: the extents, the accessors and the emitters all derive from it, so
    // the writer and the reader cannot disagree about where a field sits.
    //
    // They did disagree, and that was the whole bug. The zkVM guest keeps a
    // node's child id immediately after the tag so child()/value() is a
    // constant-offset read; this side emitted the path first. The magic, the
    // 8-byte header and the RLP envelope all matched, so every structural check
    // passed while the guest parsed one node, landed mid-field and aborted --
    // exit 0, a plausible step count, and 256 zero bytes where its public values
    // belong.
    inline unsigned char const *payload(unsigned char const *const p)
    {
        return p + 1;
    }

    // One past the tag's fixed-width run: where the path starts for the tags
    // that have one, and the end of the node for the tags that do not.
    inline unsigned char const *fixed_end(unsigned char const *const p)
    {
        switch (Tag(*p)) {
        case BRANCH: // 16 child offsets
            return payload(p) + 16 * sizeof(uint32_t);
        case EXT: // child offset
            return payload(p) + sizeof(uint32_t);
        case LEAF_STORAGE: // 32-byte value
            return payload(p) + 32;
        case LEAF_ACCT: { // storage offset, code-hash RLP, nonce | balance run
            unsigned char const *const len_p =
                payload(p) + sizeof(uint32_t) + HASH_RLP_LEN;
            return len_p + 1 + *len_p;
        }
        case DIGEST: // 32-byte hash
            return payload(p) + 32;
        }
        MONAD_ABORT("offset trie: invalid node tag");
    }

    inline bool has_path(unsigned char const *const p)
    {
        Tag const t = Tag(*p);
        return t == EXT || t == LEAF_ACCT || t == LEAF_STORAGE;
    }

    // The path: a nibble count then ceil(nlen/2) packed nibbles, at fixed_end().
    inline unsigned path_nlen(unsigned char const *const p)
    {
        return *fixed_end(p);
    }

    inline unsigned path_bytes(unsigned char const *const p)
    {
        return (path_nlen(p) + 1) / 2;
    }

    inline mpt::NibblesView path_view(unsigned char const *const p)
    {
        return mpt::NibblesView{0u, path_nlen(p), fixed_end(p) + 1};
    }

    inline byte_string_view byte_string_path_view(unsigned char const *const p)
    {
        return byte_string_view{fixed_end(p) + 1, path_bytes(p)};
    }

    inline unsigned char const *NodeViewBase::end() const
    {
        // Derived, not a second switch: one layout, one place. The copy that used
        // to live here was the other half of the disagreement above.
        return has_path(p_) ? fixed_end(p_) + 1 + path_bytes(p_) : fixed_end(p_);
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
            return NodeId{rd_u32(payload(p_))};
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

        NodeId storage() const // NULL_ID if no storage subtree materialized
        {
            return NodeId{rd_u32(payload(p_))};
        }

        // The leaf is DECOMPOSED: it holds the code hash, the nonce and the
        // balance, and no storage root -- storage() is the root. So there is no
        // account RLP to hand back, and nothing re-encodes one to read a field.
        byte_string_view code_hash_rlp() const
        {
            return byte_string_view{
                payload(p_) + sizeof(uint32_t), HASH_RLP_LEN};
        }

        byte_string_view nonce_balance_rlp() const
        {
            unsigned char const *const len_p =
                payload(p_) + sizeof(uint32_t) + HASH_RLP_LEN;
            size_t const len = len_p[0];
            MONAD_ASSERT(len >= 2 && len <= MAX_NONCE_BALANCE_RLP_LEN);
            return byte_string_view{len_p + 1, len};
        }

        // lazily RLP-decode the account (fields for read_account)
        Account account() const
        {
            Account acct;
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

        mpt::NibblesView path() const
        {
            return path_view(p_);
        }

        bytes32_t value() const
        {
            bytes32_t v;
            std::memcpy(v.bytes, payload(p_), 32);
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
        // No storage root parameter: the leaf takes it from its storage edge,
        // which is why a decomposed leaf never stores one.
        NodeId put_acct(NodeId, mpt::NibblesView, Account const &, NodeId);
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
        // Re-pathing an account leaf: everything up to the path is copied
        // verbatim, so it neither decodes nor re-encodes the account. Only
        // possible because the path comes LAST.
        NodeId clone_acct(
            NodeId id, byte_string_view prefix, mpt::NibblesView new_path);

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
