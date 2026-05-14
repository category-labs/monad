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
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <cstdint>
#include <mutex>

namespace monad::mpt
{
    class Db;
}

MONAD_NAMESPACE_BEGIN

/// In-memory sparse Ethereum account+storage MPT, populated incrementally
/// from monad's on-disk `mpt::Db` along the paths a block writes. Once the
/// paths the block touches are resolved, `compute_state_root` produces the
/// post-block Ethereum-canonical state root entirely in memory — no disk I/O
/// required.
///
/// HashCache is a sibling of `AccountsCache` / `StorageCache` inside
/// `DbCache`. The three caches together hold the per-block working set the
/// executor needs:
///   - AccountsCache: addr -> (optional) Account
///   - StorageCache:  (addr,incarnation,slot) -> bytes32 value
///   - HashCache:     a sparse MPT mirroring the canonical accounts trie,
///                    keyed by trie path (= nibbles of keccak256(addr) and,
///                    inside a per-account storage subtree, keccak256(slot)).
///
/// The in-memory trie stores `mpt::Node`-derived `PartialNode<V>` data
/// (extension / branch / leaf, plus `HashStub` placeholders for unresolved
/// subtrees). Sibling subtrees that the block doesn't touch remain as
/// `HashStub` and contribute to the state-root hash via their cached
/// child-hash bytes.
class HashCache final
{
    AccountTrie root_;
    std::mutex mu_; ///< protects root_ under concurrent fiber prefetch

public:
    HashCache();
    ~HashCache();

    HashCache(HashCache const &) = delete;
    HashCache &operator=(HashCache const &) = delete;
    HashCache(HashCache &&) = delete;
    HashCache &operator=(HashCache &&) = delete;

    /// Drop any cached structure and re-seed with an unresolved trie rooted
    /// at the given pre-state hash. Call once per block, before execution.
    void reset(bytes32_t const &pre_state_root);

    /// Resolve the path to `addr` by walking the on-disk trie via `db.find`
    /// and replacing any HashStubs along the path with the translated
    /// canonical subtree. Idempotent: re-prefetching an already-resolved
    /// path is a no-op. Safe to call from multiple fibers concurrently.
    void prefetch_account(
        mpt::Db &db, mpt::Node::SharedPtr const &on_disk_root,
        mpt::NibblesView state_prefix, uint64_t block_number,
        Address const &addr);

    /// Resolve the storage path (addr, slot) by walking into the per-account
    /// storage subtree of `addr` (which must have been resolved first) and
    /// replacing the appropriate HashStubs. Safe under concurrent prefetch.
    void prefetch_storage(
        mpt::Db &db, mpt::Node::SharedPtr const &on_disk_root,
        mpt::NibblesView state_prefix, uint64_t block_number,
        Address const &addr, bytes32_t const &slot);

    /// Apply block-wide state deltas to the in-memory trie and return the
    /// resulting Ethereum-canonical state root. Aborts if a path required
    /// by `deltas` was not previously prefetched (HashStub encountered on
    /// the walk).
    bytes32_t compute_state_root(StateDeltas const &deltas);
};

MONAD_NAMESPACE_END
