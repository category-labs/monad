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
    // TODO: walk into the per-account storage subtree of `addr` in root_,
    // translating and splicing storage nodes (PartialNode<StorageLeafValue>)
    // along the keccak256(slot) path. For now this only warms the on-disk
    // NodeCache via find(), and leaves the storage subtree as a HashStub
    // (which still produces the correct state_root if the storage subtree
    // isn't modified by the block).
    auto const acct_hash = keccak256({addr.bytes, sizeof(addr.bytes)});
    auto const slot_hash = keccak256({slot.bytes, sizeof(slot.bytes)});
    (void)db.find(
        on_disk_root,
        mpt::concat(
            state_prefix,
            mpt::NibblesView{acct_hash},
            mpt::NibblesView{slot_hash}),
        block_number);
}

bytes32_t HashCache::compute_state_root(StateDeltas const &deltas)
{
    std::lock_guard<std::mutex> const lk{mu_};
    apply_state_deltas_to_trie(root_, deltas);
    return compute_account_state_root(root_);
}

MONAD_NAMESPACE_END
