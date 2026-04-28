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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <array>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <variant>
#include <vector>

MONAD_NAMESPACE_BEGIN

/// An unresolved subtree whose contents are absent from the witness.
struct HashStub
{
    bytes32_t hash;
};

using NodeIndex = ankerl::unordered_dense::map<bytes32_t, byte_string>;

template <typename T>
concept LeafValue =
    requires(byte_string_view &enc, NodeIndex const &nodes, T const &v) {
        { T::decode(enc, nodes) } -> std::same_as<Result<T>>;
        { T::encode(v) } -> std::same_as<byte_string>;
    };

template <LeafValue V>
struct PartialNode;

/// Owning pointer to a child node. A null pointer represents an empty branch
/// slot (analogous to an absent nibble in a standard Ethereum branch node).
template <LeafValue V>
using ChildRef = std::unique_ptr<PartialNode<V>>;

template <LeafValue V>
struct BranchData
{
    std::array<ChildRef<V>, 16> children;
    std::optional<V> value;
};

template <LeafValue V>
struct ExtensionData
{
    mpt::Nibbles path;
    ChildRef<V> child;
};

template <LeafValue V>
struct LeafData
{
    mpt::Nibbles path;
    V value;
};

/// Four-way variant: branch, extension, leaf, or opaque hash stub.
template <LeafValue V>
struct PartialNode
{
    using Variant =
        std::variant<BranchData<V>, ExtensionData<V>, LeafData<V>, HashStub>;

    Variant v;

    PartialNode() = default;

    template <class T>
        requires std::constructible_from<Variant, T>
    explicit PartialNode(T &&x)
        : v(std::forward<T>(x))
    {
    }
};

struct StorageLeafValue
{
    bytes32_t value;

    static Result<StorageLeafValue>
    decode(byte_string_view &enc, NodeIndex const & /*nodes*/);

    static byte_string encode(StorageLeafValue const &v);
};

using StorageTrie = ChildRef<StorageLeafValue>;

struct AccountLeafValue
{
    Account account;
    StorageTrie
        storage{}; ///< per-account storage MPT, embedded directly in the leaf

    static Result<AccountLeafValue>
    decode(byte_string_view &enc, NodeIndex const &nodes);

    static byte_string encode(AccountLeafValue const &v);
};

using AccountTrie = ChildRef<AccountLeafValue>;

using CodeIndex = ankerl::unordered_dense::map<bytes32_t, vm::SharedIntercode>;

/// Output of collect_witness: pre-state trie node RLPs and the
/// bytecodes of accounts actually loaded via `read_code` during
/// execution. Nodes are naturally unique (tree traversal visits each
/// once); codes are deduped upstream in `PartialTrieDb::loaded_codes_`.
struct WitnessData
{
    std::vector<byte_string> nodes;
    std::vector<vm::SharedIntercode> codes;
};

// ---------------------------------------------------------------------------
// Access tracking
// ---------------------------------------------------------------------------

/// Records which trie nodes were touched during execution and which
/// SharedIntercodes were loaded via read_code. Consumed by collect_witness
/// to build the per-block witness.
struct AccessTracker
{
    static constexpr bool enabled = true;

    struct BranchAccess
    {
        std::array<void const *, 16> children;
        bool value;
    };

    /// Pointers to PartialNode<AccountLeafValue>/<StorageLeafValue>
    /// traversed by lookups or marked explicitly by witness collection.
    /// Stored as void const* since only identity matters.
    ankerl::unordered_dense::set<void const *> nodes;

    ankerl::unordered_dense::map<void const *, BranchAccess> deleted_siblings;

    /// Intercodes handed out by read_code since the last reset. Mirrors
    /// revm's `cache.contracts`: only real bytecode loads populate it.
    ankerl::unordered_dense::set<vm::SharedIntercode> codes;

    void mark_accessed(void const *node)
    {
        nodes.insert(node);
    }

    bool was_accessed(void const *node) const
    {
        return nodes.contains(node);
    }

    /// Pre-pass hook for mark_deletion_siblings. On the first visit to
    /// `node`, snapshot its children as an array of raw pointers (unwrapped
    /// from the unique_ptrs). Every call then nulls the slot at `idx`,
    /// recording that the corresponding child has been deleted. Any `idx` >= 16
    /// is interpreted as the branch value being deleted.
    // The post-pass scans entries for branches with a single
    /// surviving (non-null) child to mark compression promotions.
    template <LeafValue V>
    void mark_branch_deleted_child(PartialNode<V> const &ref, std::size_t idx)
    {
        auto const &node = std::get<BranchData<V>>(ref.v);

        auto const [it, inserted] = deleted_siblings.try_emplace(
            static_cast<void const *>(&ref), BranchAccess{});
        if (inserted) {
            for (unsigned i = 0; i < 16; ++i) {
                if (node.children[i]) {
                    it->second.children[i] =
                        static_cast<void const *>(node.children[i].get());
                }
            }
            if (node.value) {
                it->second.value = true;
            }
        }

        if (idx < 16) {
            it->second.children[idx] = nullptr;
        }
        else {
            it->second.value = false;
        }
    }

    unsigned live_branch_children(BranchAccess const &ba) const
    {
        unsigned live = 0;
        for (auto const *c : ba.children) {
            if (c) {
                ++live;
            }
        }
        return live;
    }

    /// Post-state of a branch in `deleted_siblings`: true when at most one
    /// slot (child or value) remains alive, i.e. the MPT branch must
    /// compress (single child).
    /// If only the child value remains, compression will happen but we
    /// don't need to mark any children.
    bool will_branch_compress(void const *ref) const
    {
        auto const it = deleted_siblings.find(ref);
        if (it == deleted_siblings.end()) {
            return false;
        }
        return live_branch_children(it->second) == 1 && !it->second.value;
    }

    /// Post-state of a branch in `deleted_siblings`: true when *every*
    /// slot has been drained (no live children, no value). Distinct from
    /// `will_branch_compress` — an empty branch's parent-slot becomes
    /// null (so compression propagates upward), whereas a compressed branch
    /// still occupies its parent's slot (just in reshaped form).
    bool is_branch_empty(void const *ref) const
    {
        auto const it = deleted_siblings.find(ref);
        if (it == deleted_siblings.end()) {
            return false;
        }
        return live_branch_children(it->second) == 0 && !it->second.value;
    }

    void mark_code(vm::SharedIntercode const &code)
    {
        codes.insert(code);
    }

    auto const &loaded_codes() const
    {
        return codes;
    }

    void reset()
    {
        nodes.clear();
        codes.clear();
        deleted_siblings.clear();
    }
};

/// Empty tag type. Every recording call site is guarded by
/// `if constexpr (Tracker::enabled)`, so a PartialTrieDb parameterised on
/// NoopAccessTracker emits zero tracking instructions — no calls to
/// dummy/no-op functions exist at all.
struct NoopAccessTracker
{
    static constexpr bool enabled = false;
};

// ---------------------------------------------------------------------------
// PartialTrieDb
// ---------------------------------------------------------------------------

/// A sparse Ethereum account + storage MPT that implements the Db interface.
///
/// Templated on an access-tracking policy. `AccessTracker` records every
/// touched node and loaded code — use it when generating a witness.
/// `NoopAccessTracker` statically disables all tracking — use it when
/// consuming a witness. Because every recording call site is guarded by
/// `if constexpr (Tracker::enabled)`, the noop variant compiles to zero
/// tracking instructions (no calls to dummy or empty functions).
///
/// The tracker is owned externally and borrowed by reference, so callers
/// can reset or inspect its state without going through the db.
///
/// Built from a Reth witness bundle (via `from_reth_witness`, which always
/// returns the untracked variant) or default-constructed empty and populated
/// by `commit()` — a drop-in replacement for TrieDb during zkVM STF
/// proving. The trie IS the pre-state; there are no separate account or
/// storage vectors.
template <typename Tracker>
class PartialTrieDb final : public Db
{
    // Lets from_reth_witness (instantiated for any Tracker) construct the
    // NoopAccessTracker variant via the private 3-arg constructor.
    template <typename>
    friend class PartialTrieDb;

    AccountTrie root_;
    CodeIndex codes_;
    uint64_t block_number_{0};
    BlockHeader last_committed_header_{};
    Tracker &tracker_;

    PartialTrieDb(Tracker &tracker, AccountTrie root, CodeIndex codes)
        : root_{std::move(root)}
        , codes_{std::move(codes)}
        , tracker_{tracker}
    {
    }

    /// Walk the trie rooted at `root` following the given nibble key.
    /// Returns std::nullopt if the lookup hits an unresolved HashStub, a
    /// pointer to the leaf value on success, or nullptr if the key is
    /// absent. Records each traversed node in `tracker_` (elided at
    /// compile time when tracking is disabled).
    template <LeafValue V>
    std::optional<V *>
    trie_lookup(ChildRef<V> const &root, mpt::NibblesView remaining) const;

    /// Walk the trie along `key` and mark only those siblings that branch
    /// compression will promote into a path-merge with trie_delete. Returns
    /// true iff the subtree rooted at `root` becomes null after the delete;
    /// callers at enclosing branches use that to decide whether compression
    /// actually fires at their level. Handles a single delete in isolation —
    /// cascaded compression from multiple block deletes converging at the
    /// same branch is not captured here.
    template <LeafValue V>
    bool
    mark_deletion_siblings(ChildRef<V> const &root, mpt::NibblesView key) const
        requires(Tracker::enabled);

    /// Post-order traversal: encode accessed nodes, append their RLPs to
    /// `nodes`, and return the child-ref encoding (inline RLP if <32 bytes,
    /// else 32-byte hash reference). Unaccessed subtrees fall back to
    /// encode_child_ref. Each node is visited exactly once via its parent,
    /// so no dedup is required. Uses `tracker_` to decide what's accessed.
    template <LeafValue V>
    byte_string collect_accessed_nodes(
        ChildRef<V> const &child, std::vector<byte_string> &nodes) const
        requires(Tracker::enabled);

public:
    /// Construct an empty trie. The caller supplies a tracker that must
    /// outlive this db instance.
    explicit PartialTrieDb(Tracker &tracker)
        : tracker_{tracker}
    {
    }

    /// Parse a Reth-format witness. The returned db is always untracked —
    /// the witness consumer has no reason to record further accesses. Its
    /// tracker reference binds to a shared stateless singleton with static
    /// storage duration, so the returned value is safe to store and move.
    static Result<PartialTrieDb<NoopAccessTracker>> from_reth_witness(
        bytes32_t const &pre_state_root, byte_string_view encoded_nodes,
        byte_string_view encoded_codes);

    std::optional<Account> read_account(Address const &) override;

    /// Like read_account, but returns std::nullopt (outer) when the lookup
    /// hits an unresolved HashStub.
    std::optional<std::optional<Account>>
    read_account_maybe(Address const &addr);

    bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;

    /// Like read_storage, but returns std::nullopt when the lookup hits an
    /// unresolved HashStub.
    std::optional<bytes32_t>
    read_storage_maybe(Address const &addr, Incarnation, bytes32_t const &key);

    vm::SharedIntercode read_code(bytes32_t const &code_hash) override;

    BlockHeader read_eth_header() override;

    bytes32_t state_root() override;
    bytes32_t receipts_root() override;
    bytes32_t transactions_root() override;
    std::optional<bytes32_t> withdrawals_root() override;

    uint64_t get_block_number() const override;

    void set_block_and_prefix(
        uint64_t block_number,
        bytes32_t const &block_id = bytes32_t{}) override;

    void commit(
        bytes32_t const &block_id, CommitBuilder &, BlockHeader const &,
        StateDeltas const &, std::function<void(BlockHeader &)>) override;

    /// Collect pre-state trie nodes and code hashes for witness generation.
    /// Must be called AFTER execution but BEFORE commit() (which mutates the
    /// trie). `deltas` is used to mark write-only paths (not preceded by a
    /// read) and deletion siblings (needed by the witness consumer to replay
    /// branch compression). Only available when tracking is enabled.
    WitnessData collect_witness(StateDeltas const &deltas) const
        requires(Tracker::enabled);

    // No-op overrides for operations that are irrelevant in the witness
    // context.
    void finalize(uint64_t, bytes32_t const &) override {}

    void update_verified_block(uint64_t) override {}

    void update_voted_metadata(uint64_t, bytes32_t const &) override {}

    void update_proposed_metadata(uint64_t, bytes32_t const &) override {}
};

MONAD_NAMESPACE_END
