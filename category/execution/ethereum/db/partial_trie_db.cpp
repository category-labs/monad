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

#include <category/execution/ethereum/db/partial_trie_db.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <functional>
#include <optional>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Deltas cover the whole *touched* set, not the changed set: a read lands as
// `first == second` (BlockState::read_storage). An unchanged entry contributes
// nothing to the trie, but committing it anyway costs a full root-to-leaf
// descent and invalidates the cached hash of every node along it — so filter
// them out before touching the trie at all.
bool is_changed(StorageDelta const &d)
{
    return d.first != d.second;
}

bool is_changed(StateDelta const &d)
{
    if (d.account.first != d.account.second) {
        return true;
    }
    for (auto const &kv : d.storage) {
        if (is_changed(kv.second)) {
            return true;
        }
    }
    return false;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

std::optional<Account> PartialTrieDb::read_account(Address const &addr)
{
    auto const key = keccak256(addr.bytes);
    return match(
        trie_.find_original(trie_.root, mpt::NibblesView{key}),
        Cases{
            [](mpt::NullView) -> std::optional<Account> {
                return std::nullopt;
            },
            [](mpt::AccountLeafView l) -> std::optional<Account> {
                return l.account();
            },
            [](auto) -> std::optional<Account> {
                MONAD_ABORT("incorrect node type returned in read_account");
            }});
}

bytes32_t PartialTrieDb::read_storage(
    Address const &addr, Incarnation, bytes32_t const &slot)
{
    auto const akey = keccak256(addr.bytes);
    auto const sroot = match(
        trie_.find_original(trie_.root, mpt::NibblesView{akey}),
        Cases{
            [](mpt::NullView) { return mpt::NULL_ID; },
            [](mpt::AccountLeafView l) { return l.storage(); },
            [](auto) -> mpt::NodeId {
                MONAD_ABORT("incorrect node type returned in read_storage");
            }});

    if (sroot == mpt::NULL_ID) {
        return bytes32_t{};
    }
    auto const skey = keccak256(slot.bytes);

    return match(
        trie_.find_original(sroot, mpt::NibblesView{skey}),
        Cases{
            [](mpt::NullView) { return bytes32_t{}; },
            [](mpt::StorageLeafView l) { return l.value(); },
            [](auto) -> bytes32_t {
                MONAD_ABORT("incorrect node type returned in read_storage");
            }});
}

void PartialTrieDb::commit(
    bytes32_t const &, CommitBuilder &, BlockHeader const &header,
    StateDeltas const &deltas,
    std::function<void(BlockHeader &)> populate_header_fn)
{
    using mpt::NodeId;
    using mpt::NULL_ID;
    using mpt::OffsetTrie;

    block_number_ = header.number;

    // Pass 1: inserts and updates — accounts present in the post-state. The
    // storage sub-root is threaded through the put_* builders rather than held
    // as a live leaf reference.
    for (auto const &[addr, delta] : deltas) {
        auto const &new_account = delta.account.second;
        if (!new_account || !is_changed(delta)) {
            continue;
        }
        auto const acct_key = keccak256(addr.bytes);
        auto const [leaf, leaf_path] =
            trie_.upsert_node(trie_.root, mpt::NibblesView{acct_key});
        if (MONAD_UNLIKELY(trie_.root == NULL_ID)) {
            // First account into an empty trie: the leaf becomes the root.
            trie_.root = leaf;
        }
        NodeId storage = match(
            trie_.get_current(leaf),
            Cases{
                [](mpt::NullView) { return NULL_ID; },
                [](mpt::AccountLeafView a) { return a.storage(); },
                [](auto) -> NodeId {
                    MONAD_ABORT("incorrect node type returned in commit");
                }});

        // Incarnation bump (destroy + recreate in-block): wipe old storage.
        if (delta.account.first.has_value() &&
            delta.account.first->incarnation != new_account->incarnation) {
            storage = NULL_ID;
        }

        // Storage deltas: upserts first, then deletions (as in the reference).
        for (auto const &[slot, sdelta] : delta.storage) {
            if (is_changed(sdelta) && sdelta.second != bytes32_t{}) {
                auto const slot_key = keccak256(slot.bytes);
                auto const [sleaf, sleaf_path] =
                    trie_.upsert_node(storage, mpt::NibblesView{slot_key});
                if (storage == NULL_ID) {
                    storage = sleaf; // first slot into empty storage: the leaf
                                     // is the sub-root
                }
                trie_.put_storage(sleaf, sleaf_path, sdelta.second);
            }
        }
        for (auto const &[slot, sdelta] : delta.storage) {
            if (is_changed(sdelta) && sdelta.second == bytes32_t{}) {
                auto const slot_key = keccak256(slot.bytes);
                if (trie_.erase_node(storage, mpt::NibblesView{slot_key}) ==
                    OffsetTrie::EraseResult::Erased) {
                    storage = NULL_ID;
                };
            }
        }

        // Bake the freshly computed storage root into the account leaf.
        bytes32_t const storage_root = trie_.hash(storage);
        trie_.put_acct(
            leaf,
            mpt::NibblesView{leaf_path},
            *new_account,
            storage_root,
            storage);
    }

    // Pass 2: deletions — accounts absent in the post-state but present before.
    for (auto const &[addr, delta] : deltas) {
        if (delta.account.second || !delta.account.first) {
            continue;
        }
        auto const acct_key = keccak256(addr.bytes);
        if (MONAD_UNLIKELY(
                trie_.erase_node(trie_.root, mpt::NibblesView{acct_key}) ==
                OffsetTrie::EraseResult::Erased)) {
            trie_.root = NULL_ID;
        }
    }

    last_committed_header_ = header;
    MONAD_ASSERT(populate_header_fn);
    populate_header_fn(last_committed_header_);
}

MONAD_NAMESPACE_END
