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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/hash_cache.hpp>
#include <category/execution/ethereum/db/partial_node.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <cstdint>
#include <memory>
#include <mutex>

MONAD_NAMESPACE_BEGIN

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
    // TODO: Walk monad's on-disk trie down the keccak256(addr) path,
    // translate each visited mpt::Node into a canonical PartialNode<
    // AccountLeafValue>, and splice into root_ replacing HashStubs along
    // the way. For now this just warms the on-disk NodeCache via find()
    // so that subsequent reads of this account/storage are in-memory.
    auto const key_hash = keccak256({addr.bytes, sizeof(addr.bytes)});
    (void)db.find(
        on_disk_root,
        mpt::concat(state_prefix, mpt::NibblesView{key_hash}),
        block_number);
}

void HashCache::prefetch_storage(
    mpt::Db &db, mpt::Node::SharedPtr const &on_disk_root,
    mpt::NibblesView const state_prefix, uint64_t const block_number,
    Address const &addr, bytes32_t const &slot)
{
    // TODO: Walk into the per-account storage subtree of `addr` in root_,
    // translating and splicing as for prefetch_account. For now just
    // warms the on-disk NodeCache.
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
    // Apply block-wide deltas to the in-memory sparse trie, then walk it
    // RLP-encoding nodes and keccak-hashing children. Aborts if a path the
    // deltas touch was never prefetched (the walk would hit an unresolved
    // HashStub).
    apply_state_deltas_to_trie(root_, deltas);
    return compute_account_state_root(root_);
}

MONAD_NAMESPACE_END
