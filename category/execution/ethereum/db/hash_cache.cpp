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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/hash_cache.hpp>
#include <category/execution/ethereum/db/partial_node.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <cstdint>
#include <cstring>
#include <memory>
#include <mutex>
#include <utility>
#include <variant>

MONAD_NAMESPACE_BEGIN

namespace
{
    /// Account-trie canonical depth at which we cross from accounts trie to
    /// storage subtree (= length of keccak256 in nibbles).
    constexpr unsigned ACCOUNT_BOUNDARY = 64;

    /// Build a HashStub PartialNode<V> from a child_data_view byte_string_view.
    /// Asserts the view is exactly 32 bytes (the inline-encoding case, where
    /// the child's RLP is < 32 bytes and stored inline, is left as a TODO —
    /// it would require decoding the inline RLP into a PartialNode subtree).
    template <LeafValue V>
    ChildRef<V> make_hash_stub(byte_string_view const child_data)
    {
        MONAD_ASSERT(child_data.size() == 32);
        bytes32_t hash;
        std::memcpy(hash.bytes, child_data.data(), 32);
        return std::make_unique<PartialNode<V>>(HashStub{hash});
    }

    /// Translate an accounts-trie mpt::Node at canonical `start_depth` into
    /// an Ethereum-canonical PartialNode<AccountLeafValue>. Sibling slots
    /// become HashStubs sourced from `child_data_view`; the slot on the
    /// target path is left nullptr (the walker will recurse into it). At the
    /// account boundary (start_depth + path_len == 64), the node is the
    /// account leaf: decode the value to recover the Account, take the
    /// canonical storage_root from node.data(), and wrap as a Leaf whose
    /// AccountLeafValue.storage is a HashStub.
    ///
    /// KNOWN LIMITATION: monad's flat trie can contain a "Branch with empty
    /// bookkeeping value + a single child" at internal levels (e.g. the
    /// state-subtree root when only one account exists). Canonical Ethereum
    /// MPT collapses single-child branches into Extension/Leaf nodes by
    /// merging the implicit branch nibble into the child path. This
    /// translator does NOT yet perform that collapse, so the produced
    /// state_root will diverge from `TrieDb::state_root()` whenever the
    /// trie contains any single-child interior monad node above the
    /// boundary. Symptom: a state with only a small number of accounts (or
    /// with deep single-child interior chains) will round-trip incorrectly.
    /// Real production tries with many accounts are typically multi-child
    /// at the top, so this works for the common case — but the collapse
    /// has to land before HashCache can be wired into execute_block.
    ChildRef<AccountLeafValue> translate_account_node(
        mpt::Node const &n, unsigned const start_depth,
        unsigned const next_nibble_on_path)
    {
        mpt::NibblesView const path = n.path_nibble_view();
        unsigned const end_depth = start_depth + path.nibble_size();

        if (end_depth == ACCOUNT_BOUNDARY && n.has_value()) {
            // Account leaf. The monad-internal value is encode_account_db
            // output (Address || canonical-account-RLP); strip the address.
            byte_string_view enc = n.value();
            auto acct_res = decode_account_db_ignore_address(enc);
            MONAD_ASSERT(!acct_res.has_error());
            Account const acct = acct_res.value();

            // n.data() caches the canonical storage-trie root hash for a
            // leaf-with-children node (the boundary case).
            byte_string_view const data_view = n.data();
            StorageTrie storage_trie;
            if (data_view.size() == 32) {
                bytes32_t storage_root;
                std::memcpy(storage_root.bytes, data_view.data(), 32);
                if (storage_root != NULL_ROOT) {
                    storage_trie =
                        std::make_unique<PartialNode<StorageLeafValue>>(
                            HashStub{storage_root});
                }
            }
            // else: data_len 0 means an empty / no-storage account; leave
            // storage_trie as null (encodes to NULL_ROOT in the account RLP).

            return std::make_unique<PartialNode<AccountLeafValue>>(
                LeafData<AccountLeafValue>{
                    mpt::Nibbles{path},
                    AccountLeafValue{acct, std::move(storage_trie)}});
        }

        // Interior node: build a canonical BranchData and (if path is
        // non-empty) wrap in an ExtensionData. The sibling slots are
        // HashStubs from child_data_view; the slot on the target path is
        // left null so the walker can recurse and translate the next mpt
        // node into it.
        BranchData<AccountLeafValue> branch{};
        for (unsigned nibble = 0; nibble < 16; ++nibble) {
            if (!(n.mask & (1U << nibble))) {
                continue;
            }
            if (nibble == next_nibble_on_path) {
                // leave null; walker will fill in via recursion
                continue;
            }
            unsigned const idx = n.to_child_index(nibble);
            branch.children[nibble] =
                make_hash_stub<AccountLeafValue>(n.child_data_view(idx));
        }

        auto branch_node =
            std::make_unique<PartialNode<AccountLeafValue>>(std::move(branch));

        if (path.nibble_size() > 0) {
            return std::make_unique<PartialNode<AccountLeafValue>>(
                ExtensionData<AccountLeafValue>{
                    mpt::Nibbles{path}, std::move(branch_node)});
        }
        return branch_node;
    }

    /// Walk both `partial_ref` (a slot inside HashCache's sparse trie) and
    /// `mpt_node` (the corresponding on-disk node, hydrated by a prior
    /// find()) down the target path, translating mpt::Nodes into the
    /// canonical PartialNode<AccountLeafValue> form. Stops when the leaf
    /// is reached, the path diverges, or the cache already holds a fully
    /// resolved subtree along the path.
    void walk_account_path(
        ChildRef<AccountLeafValue> &partial_ref,
        mpt::Node::SharedPtr const &mpt_node, unsigned const start_depth,
        mpt::NibblesView const target_remaining)
    {
        if (!mpt_node) {
            // The on-disk side has nothing here; nothing to resolve.
            return;
        }

        // What's the next nibble on the path we're heading toward? The
        // translator stamps a `null` placeholder for that slot so we can
        // distinguish it from sibling HashStubs.
        unsigned const path_len = mpt_node->path_nibble_view().nibble_size();
        unsigned const after_path_depth = start_depth + path_len;
        unsigned const next_nibble = (after_path_depth < ACCOUNT_BOUNDARY &&
                                      target_remaining.nibble_size() > path_len)
                                         ? target_remaining.get(path_len)
                                         : 16U; // sentinel: no descent

        // If the partial_ref is null or a HashStub, translate the on-disk
        // node into place. Otherwise the cache already has a real subtree
        // here from a previous prefetch — leave it untouched and descend.
        if (!partial_ref || std::holds_alternative<HashStub>(partial_ref->v)) {
            partial_ref =
                translate_account_node(*mpt_node, start_depth, next_nibble);
        }

        // If we landed on a leaf or no further descent is possible, done.
        if (next_nibble == 16U) {
            return;
        }
        if (std::holds_alternative<LeafData<AccountLeafValue>>(
                partial_ref->v)) {
            return;
        }

        // The translator either built an Extension(path) wrapping a Branch
        // or a bare Branch. Descend to the Branch, then into the targeted
        // child slot.
        BranchData<AccountLeafValue> *branch = nullptr;
        if (auto *ext =
                std::get_if<ExtensionData<AccountLeafValue>>(&partial_ref->v)) {
            MONAD_ASSERT(ext->child);
            branch = std::get_if<BranchData<AccountLeafValue>>(&ext->child->v);
        }
        else {
            branch = std::get_if<BranchData<AccountLeafValue>>(&partial_ref->v);
        }
        MONAD_ASSERT(branch);

        // Move to the next mpt::Node in lockstep. The on-disk children are
        // stored in packed order (one entry per set mask bit).
        unsigned const mpt_child_idx = mpt_node->to_child_index(next_nibble);
        mpt::Node::SharedPtr const &next_mpt = mpt_node->next(mpt_child_idx);

        walk_account_path(
            branch->children[next_nibble],
            next_mpt,
            after_path_depth + 1,
            target_remaining.substr(path_len + 1));
    }

    /// Find the AccountLeafValue at the given target nibble path in HashCache's
    /// sparse account trie. Returns nullptr if the path isn't fully resolved
    /// (the walk hit a HashStub or null), the path diverges from cached
    /// structure, or the account isn't present.
    AccountLeafValue *
    find_account_leaf_mut(AccountTrie &root, mpt::NibblesView remaining)
    {
        PartialNode<AccountLeafValue> *node = root.get();
        while (node != nullptr) {
            if (auto *leaf =
                    std::get_if<LeafData<AccountLeafValue>>(&node->v)) {
                return (mpt::NibblesView{leaf->path} == remaining)
                           ? &leaf->value
                           : nullptr;
            }
            if (auto *ext =
                    std::get_if<ExtensionData<AccountLeafValue>>(&node->v)) {
                mpt::NibblesView const ext_path{ext->path};
                if (!remaining.starts_with(ext_path)) {
                    return nullptr;
                }
                remaining = remaining.substr(ext_path.nibble_size());
                node = ext->child.get();
            }
            else if (
                auto *branch =
                    std::get_if<BranchData<AccountLeafValue>>(&node->v)) {
                if (remaining.empty()) {
                    return branch->value ? &*branch->value : nullptr;
                }
                unsigned const nibble = remaining.get(0);
                remaining = remaining.substr(1);
                node = branch->children[nibble].get();
            }
            else {
                // HashStub: account-path not yet fully translated.
                return nullptr;
            }
        }
        return nullptr;
    }

    /// Translate a storage-trie mpt::Node at canonical storage-depth
    /// `start_depth` into PartialNode<StorageLeafValue>. Mirrors
    /// translate_account_node but for storage: the leaf boundary is at
    /// storage-depth 64 (= flat depth 128), and the leaf value is the
    /// bytes32_t storage value decoded from monad's encode_storage_db format.
    ChildRef<StorageLeafValue> translate_storage_node(
        mpt::Node const &n, unsigned const start_depth,
        unsigned const next_nibble_on_path)
    {
        constexpr unsigned STORAGE_LEAF_DEPTH = 64;
        mpt::NibblesView const path = n.path_nibble_view();
        unsigned const end_depth = start_depth + path.nibble_size();

        if (end_depth == STORAGE_LEAF_DEPTH && n.has_value()) {
            byte_string_view enc = n.value();
            auto pair_res = decode_storage_db(enc);
            MONAD_ASSERT(!pair_res.has_error());
            bytes32_t const value = pair_res.value().second;
            return std::make_unique<PartialNode<StorageLeafValue>>(
                LeafData<StorageLeafValue>{
                    mpt::Nibbles{path}, StorageLeafValue{value}});
        }

        BranchData<StorageLeafValue> branch{};
        for (unsigned nibble = 0; nibble < 16; ++nibble) {
            if (!(n.mask & (1U << nibble))) {
                continue;
            }
            if (nibble == next_nibble_on_path) {
                continue;
            }
            unsigned const idx = n.to_child_index(nibble);
            branch.children[nibble] =
                make_hash_stub<StorageLeafValue>(n.child_data_view(idx));
        }

        auto branch_node =
            std::make_unique<PartialNode<StorageLeafValue>>(std::move(branch));
        if (path.nibble_size() > 0) {
            return std::make_unique<PartialNode<StorageLeafValue>>(
                ExtensionData<StorageLeafValue>{
                    mpt::Nibbles{path}, std::move(branch_node)});
        }
        return branch_node;
    }

    /// Walk a storage-trie path with the canonical storage trie root already
    /// in place (i.e. not a HashStub at the top). Same shape as
    /// walk_account_path but in the storage subtree.
    void walk_storage_inner(
        ChildRef<StorageLeafValue> &partial_ref,
        mpt::Node::SharedPtr const &mpt_node, unsigned const start_depth,
        mpt::NibblesView const target_remaining)
    {
        constexpr unsigned STORAGE_LEAF_DEPTH = 64;
        if (!mpt_node) {
            return;
        }
        unsigned const path_len = mpt_node->path_nibble_view().nibble_size();
        unsigned const after_path_depth = start_depth + path_len;
        unsigned const next_nibble = (after_path_depth < STORAGE_LEAF_DEPTH &&
                                      target_remaining.nibble_size() > path_len)
                                         ? target_remaining.get(path_len)
                                         : 16U;

        if (!partial_ref || std::holds_alternative<HashStub>(partial_ref->v)) {
            partial_ref =
                translate_storage_node(*mpt_node, start_depth, next_nibble);
        }

        if (next_nibble == 16U) {
            return;
        }
        if (std::holds_alternative<LeafData<StorageLeafValue>>(
                partial_ref->v)) {
            return;
        }

        BranchData<StorageLeafValue> *branch = nullptr;
        if (auto *ext =
                std::get_if<ExtensionData<StorageLeafValue>>(&partial_ref->v)) {
            MONAD_ASSERT(ext->child);
            branch = std::get_if<BranchData<StorageLeafValue>>(&ext->child->v);
        }
        else {
            branch = std::get_if<BranchData<StorageLeafValue>>(&partial_ref->v);
        }
        MONAD_ASSERT(branch);

        unsigned const mpt_child_idx = mpt_node->to_child_index(next_nibble);
        mpt::Node::SharedPtr const &next_mpt = mpt_node->next(mpt_child_idx);

        walk_storage_inner(
            branch->children[next_nibble],
            next_mpt,
            after_path_depth + 1,
            target_remaining.substr(path_len + 1));
    }

    /// Prepend a single nibble `x` to whatever path-bearing node sits at the
    /// top of `node`, returning a new ChildRef with the collapsed path. Used
    /// to merge the implicit boundary-branch nibble into the canonical
    /// single-child storage subtree root.
    ChildRef<StorageLeafValue> prepend_nibble_to_storage_node(
        unsigned char const x, ChildRef<StorageLeafValue> node)
    {
        if (!node) {
            return nullptr;
        }
        return std::visit(
            Cases{
                [&](LeafData<StorageLeafValue> &leaf)
                    -> ChildRef<StorageLeafValue> {
                    mpt::Nibbles new_path =
                        mpt::concat(x, mpt::NibblesView{leaf.path});
                    return std::make_unique<PartialNode<StorageLeafValue>>(
                        LeafData<StorageLeafValue>{
                            std::move(new_path), std::move(leaf.value)});
                },
                [&](ExtensionData<StorageLeafValue> &ext)
                    -> ChildRef<StorageLeafValue> {
                    mpt::Nibbles new_path =
                        mpt::concat(x, mpt::NibblesView{ext.path});
                    return std::make_unique<PartialNode<StorageLeafValue>>(
                        ExtensionData<StorageLeafValue>{
                            std::move(new_path), std::move(ext.child)});
                },
                [&](BranchData<StorageLeafValue> &branch)
                    -> ChildRef<StorageLeafValue> {
                    mpt::Nibbles new_path{1};
                    new_path.set(0, x);
                    return std::make_unique<PartialNode<StorageLeafValue>>(
                        ExtensionData<StorageLeafValue>{
                            std::move(new_path),
                            std::make_unique<PartialNode<StorageLeafValue>>(
                                std::move(branch))});
                },
                [&](HashStub &stub) -> ChildRef<StorageLeafValue> {
                    mpt::Nibbles new_path{1};
                    new_path.set(0, x);
                    return std::make_unique<PartialNode<StorageLeafValue>>(
                        ExtensionData<StorageLeafValue>{
                            std::move(new_path),
                            std::make_unique<PartialNode<StorageLeafValue>>(
                                stub)});
                },
            },
            node->v);
    }

    /// Drive storage-trie prefetch from the boundary account mpt::Node down to
    /// the target slot. Handles three boundary shapes:
    ///   - 0 children: account has no storage; nothing to do (storage_ref
    ///     stays as HashStub{NULL_ROOT-or-actual} or null).
    ///   - exactly 1 child at nibble X: canonical storage-trie root is the
    ///     translated child with X collapsed into its top path. If
    ///     target's first nibble == X, the descent into the child carries the
    ///     remaining target path; otherwise the slot doesn't exist.
    ///   - 2+ children: canonical storage-trie root is a Branch with each
    ///     boundary-child slot populated. The target slot is descended into
    ///     via walk_storage_inner.
    ///
    /// On a re-prefetch (storage_ref already structured), the existing root is
    /// reused: for a multi-child Branch root, the target slot is descended via
    /// walk_storage_inner; for a single-child collapsed root, any subsequent
    /// target either follows the same X-prefix (already fully resolved) or
    /// doesn't exist — so no further work is needed.
    void walk_storage_from_boundary(
        StorageTrie &storage_ref, mpt::Node::SharedPtr const &boundary_node,
        mpt::NibblesView const target_slot_path)
    {
        if (!boundary_node || target_slot_path.nibble_size() == 0) {
            return;
        }
        unsigned const child_count = boundary_node->number_of_children();
        if (child_count == 0) {
            return;
        }
        unsigned const target_first = target_slot_path.get(0);
        bool const target_in_trie =
            (boundary_node->mask & (1U << target_first)) != 0;

        bool const fresh =
            !storage_ref || std::holds_alternative<HashStub>(storage_ref->v);

        if (fresh) {
            if (child_count >= 2) {
                // Multi-child: build canonical Branch root with siblings as
                // HashStubs; leave target slot null for descent below.
                BranchData<StorageLeafValue> branch{};
                for (unsigned nibble = 0; nibble < 16; ++nibble) {
                    if (!(boundary_node->mask & (1U << nibble))) {
                        continue;
                    }
                    if (nibble == target_first && target_in_trie) {
                        continue;
                    }
                    unsigned const idx = boundary_node->to_child_index(nibble);
                    branch.children[nibble] = make_hash_stub<StorageLeafValue>(
                        boundary_node->child_data_view(idx));
                }
                storage_ref = std::make_unique<PartialNode<StorageLeafValue>>(
                    std::move(branch));
                // fall through to descent
            }
            else {
                // child_count == 1: translate the single child subtree, then
                // collapse the boundary's nibble into its top path. Recursion
                // descent is folded into the translation: if target matches X,
                // pass the remaining slot path; otherwise pass empty.
                unsigned single_nibble = 0;
                for (unsigned i = 0; i < 16; ++i) {
                    if (boundary_node->mask & (1U << i)) {
                        single_nibble = i;
                        break;
                    }
                }
                unsigned const idx =
                    boundary_node->to_child_index(single_nibble);
                mpt::Node::SharedPtr const &child_mpt =
                    boundary_node->next(idx);

                ChildRef<StorageLeafValue> child_translated;
                mpt::NibblesView const remaining =
                    (single_nibble == target_first) ? target_slot_path.substr(1)
                                                    : mpt::NibblesView{};
                walk_storage_inner(
                    child_translated,
                    child_mpt,
                    /*start_depth=*/1,
                    remaining);
                storage_ref = prepend_nibble_to_storage_node(
                    static_cast<unsigned char>(single_nibble),
                    std::move(child_translated));
                return; // single-child path complete
            }
        }

        // Descent: only valid when the storage trie root is a multi-child
        // Branch and the target nibble has an entry. (Single-child collapsed
        // roots are fully resolved along their one path during fresh build;
        // any re-prefetch on a different first nibble is a non-existent slot.)
        if (!target_in_trie) {
            return;
        }
        auto *branch =
            std::get_if<BranchData<StorageLeafValue>>(&storage_ref->v);
        if (branch == nullptr) {
            return;
        }
        unsigned const target_idx = boundary_node->to_child_index(target_first);
        mpt::Node::SharedPtr const &target_child_mpt =
            boundary_node->next(target_idx);
        walk_storage_inner(
            branch->children[target_first],
            target_child_mpt,
            /*start_depth=*/1,
            target_slot_path.substr(1));
    }
}

HashCache::HashCache() = default;
HashCache::~HashCache() = default;

void HashCache::reset(bytes32_t const &pre_state_root)
{
    std::lock_guard<std::mutex> const lk{mu_};
    if (pre_state_root == NULL_ROOT) {
        root_.reset();
    }
    else {
        root_ = std::make_unique<PartialNode<AccountLeafValue>>(
            HashStub{pre_state_root});
    }
}

void HashCache::prefetch_account(
    mpt::Db &db, mpt::Node::SharedPtr const &on_disk_root,
    mpt::NibblesView const state_prefix, uint64_t const block_number,
    Address const &addr)
{
    auto const key_hash = keccak256({addr.bytes, sizeof(addr.bytes)});
    mpt::NibblesView const target_path{key_hash};

    // Warm the on-disk path so .next() pointers are populated for in-memory
    // walking below. find() may wait on a fiber future.
    auto const full_path = mpt::concat(state_prefix, target_path);
    auto const find_res = db.find(on_disk_root, full_path, block_number);
    (void)find_res; // failure just means the account isn't in the trie

    // Locate the on-disk state-subtree root node by walking from on_disk_root
    // through state_prefix. The state_prefix is short (typically 1-2 nibbles:
    // FINALIZED_NIBBLE then STATE_NIBBLE) so a re-walk is cheap.
    auto const state_root_cursor =
        db.find(on_disk_root, state_prefix, block_number);
    if (!state_root_cursor.has_value()) {
        return;
    }
    mpt::Node::SharedPtr const state_root_node = state_root_cursor.value().node;

    std::lock_guard<std::mutex> const lk{mu_};
    walk_account_path(root_, state_root_node, 0, target_path);
}

void HashCache::prefetch_storage(
    mpt::Db &db, mpt::Node::SharedPtr const &on_disk_root,
    mpt::NibblesView const state_prefix, uint64_t const block_number,
    Address const &addr, bytes32_t const &slot)
{
    auto const acct_hash = keccak256({addr.bytes, sizeof(addr.bytes)});
    auto const slot_hash = keccak256({slot.bytes, sizeof(slot.bytes)});
    mpt::NibblesView const target_acct{acct_hash};
    mpt::NibblesView const target_slot{slot_hash};

    // Ensure the on-disk path is fully warmed before we walk in-memory.
    (void)db.find(
        on_disk_root,
        mpt::concat(state_prefix, target_acct, target_slot),
        block_number);

    // Ensure the account leaf is resolved in our sparse trie. Idempotent
    // when already resolved.
    prefetch_account(db, on_disk_root, state_prefix, block_number, addr);

    // Look up the boundary mpt::Node (depth 64 of monad's state subtree).
    auto const state_root_cursor =
        db.find(on_disk_root, state_prefix, block_number);
    if (!state_root_cursor.has_value()) {
        return;
    }
    mpt::Node::SharedPtr const state_root_node = state_root_cursor.value().node;
    auto const boundary_cursor =
        db.find(state_root_node, target_acct, block_number);
    if (!boundary_cursor.has_value()) {
        // Account doesn't exist on-disk; nothing to prefetch.
        return;
    }
    mpt::Node::SharedPtr const boundary_node = boundary_cursor.value().node;

    std::lock_guard<std::mutex> const lk{mu_};

    // Walk into our trie to locate the AccountLeafValue for this address.
    AccountLeafValue *const acct_leaf =
        find_account_leaf_mut(root_, target_acct);
    if (acct_leaf == nullptr) {
        // Account-trie path didn't resolve to a leaf (e.g. account doesn't
        // exist in the trie). Nothing to do for storage.
        return;
    }

    walk_storage_from_boundary(acct_leaf->storage, boundary_node, target_slot);
}

bytes32_t HashCache::compute_state_root(StateDeltas const &deltas)
{
    std::lock_guard<std::mutex> const lk{mu_};
    apply_state_deltas_to_trie(root_, deltas);
    return compute_account_state_root(root_);
}

MONAD_NAMESPACE_END
