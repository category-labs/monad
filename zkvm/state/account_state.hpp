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

// The rows of the guest state: one AccountState per address this block has
// touched, holding the live account, the trie positions of its pre-state and
// every storage slot the block has read or written. Rows never move, so the
// journal and the slot maps hold pointers to them.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/code.hpp>
#include <zkvm/state/key_hash.hpp>
#include <zkvm/state/slot_map.hpp>

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

// The guest types shadow native names (AccountState in particular); they
// never meet the native ones in a translation unit but keep their own
// namespace so that stays true by construction.
namespace zkvm
{
    class Journal;

    // The answer of the one account-trie walk for an address, decided once.
    // The EVM-facing layer only ever sees Present or Absent; Unproven aborts
    // at the point of use, since a witness that lacks the leaf cannot prove
    // either way.
    enum class AccountResolution : uint8_t
    {
        Unproven,
        Absent,
        Present,
    };

    // The stamp of every account decoded from the witness. The block number
    // is never zero, so no transaction's stamp can equal it.
    inline Incarnation const WITNESS_INCARNATION{0, 0};

    // A keccak digest as the trie path it spells.
    inline mpt::NibblesView key_path(bytes32_t const &hash)
    {
        return mpt::NibblesView{
            byte_string_view{hash.bytes, sizeof(hash.bytes)}};
    }

    // A persistent storage slot this block has touched, read or written.
    struct SlotState
    {
        bytes32_t key{};
        // keccak(key), computed by the storage walk that sets `resolved` and
        // kept for commit.
        bytes32_t key_hash{};
        // Value in the pre-state trie, zero if absent: what commit compares
        // `current` against. Valid once `resolved`, which the first read or
        // write sets by walking the storage subtree; a slot that is only
        // warmed never walks it.
        bytes32_t block_start{};
        // Value at the start of the current transaction, the EIP-2200
        // "original" for SSTORE gas and refunds. Meaningful once `written`
        // and while `incarnation` is the account's; before that the
        // transaction-start value is what the slot reads as. Set by the
        // first write of a block or of a new incarnation, then refreshed
        // when the epoch is stale from the value the slot then reads as.
        bytes32_t tx_start{};
        bytes32_t current{};
        // The account's incarnation at the last write. A mismatch means the
        // account was re-created since, and the slot reads as zero.
        Incarnation incarnation{0, 0};
        // The State epoch that last reset the transaction-scoped fields.
        uint64_t epoch{0};
        bool resolved{false};
        // The slot's warmth (EIP-2929): the row is the warm set.
        bool accessed{false};
        // Sticky for the block: makes the slot a commit candidate.
        bool written{false};
    };

    // A transient (EIP-1153) slot. Cleared as a whole at the transaction
    // boundary, never erased singly: a reverted first write leaves a zero,
    // which reads the same as absence.
    struct TransientSlot
    {
        bytes32_t key{};
        bytes32_t value{};
    };

    // One row per address for the whole block. Rows are never moved or
    // erased, so the journal can hold pointers to them.
    struct AccountState
    {
        // The slot maps key their indexes with the State's seed.
        explicit AccountState(KeySeed const &seed) noexcept
            : storage{seed}
            , transient_storage{seed}
        {
        }

        // The account, aborting on an unproven row: the witness cannot say
        // whether the account exists, so nothing about it may be read. The
        // warmth, touch and destruct bits need no account and are read
        // directly.
        std::optional<Account> const &account() const
        {
            if (MONAD_UNLIKELY(resolution == AccountResolution::Unproven)) {
                MONAD_ABORT("zkvm State: account not in the witness");
            }
            return account_;
        }

        std::optional<Account> &account()
        {
            if (MONAD_UNLIKELY(resolution == AccountResolution::Unproven)) {
                MONAD_ABORT("zkvm State: account not in the witness");
            }
            return account_;
        }

        // Whether a written slot's value is this account's: false once the
        // account was destroyed or re-created after the write.
        bool stamp_is_live(SlotState const &) const;
        // Hash the key and walk the storage subtree once, filling
        // `block_start`. False when the walk hits a digest: the witness
        // does not prove the slot either way, and the slot stays unresolved.
        bool resolve_slot(SlotState &, mpt::OffsetTrie const &) const;
        // What the slot reads as now, resolving the witness value on first
        // need; the account must be present. Aborts on an unproven slot.
        bytes32_t const &
        current_value(SlotState &, mpt::OffsetTrie const &) const;
        // The same, answering nullptr for an unproven slot.
        bytes32_t const *
        try_current_value(SlotState &, mpt::OffsetTrie const &) const;
        // The EIP-2200 original: what the slot read as when the transaction
        // began.
        bytes32_t const &
        tx_original_value(SlotState &, mpt::OffsetTrie const &) const;

        AccountResolution resolution{AccountResolution::Unproven};
        // The State epoch that last reset accessed, touched, destructed and
        // transient_storage. A stale value triggers begin_epoch on first
        // touch.
        uint64_t epoch{0};
        // Transaction-scoped (reset by begin_epoch).
        bool accessed{false};
        bool touched{false};
        bool destructed{false};
        // Block-scoped, sticky: set by the first account or storage write,
        // journalled or not, and never cleared. The only thing that makes
        // the row a commit candidate; a rolled-back write just decodes equal
        // there.
        bool written{false};
        // keccak(address), computed at the first lookup, reused by commit.
        bytes32_t addr_hash{};
        // Trie positions from the walk. `leaf` doubles as the pre-state
        // account: commit decodes it rather than keeping a second copy.
        mpt::NodeId leaf{mpt::NULL_ID};
        mpt::NodeId storage_root{mpt::NULL_ID};
        // The code table's entry for the account's code, resolved once per
        // distinct code hash: `code` serves while `resolved_code_hash` still
        // equals the account's, so a changed or rolled-back hash re-resolves.
        // The table is a segmented map and never erases, so the pointer
        // outlives every later insertion.
        vm::SharedVarcode const *code{nullptr};
        bytes32_t resolved_code_hash{};
        // All persistent slots this block has touched, in creation order.
        SlotMap<SlotState> storage;
        // Cleared by epoch, journalled per write. Indexed like `storage`:
        // TSTORE is cheap enough to fill a vector a scan could not handle.
        SlotMap<TransientSlot> transient_storage;

    private:
        friend class State;
        friend class Journal;

        // The live value, behind account() for everyone but the State's
        // own walk, stamp checks and rollback, which know the row is proven.
        // Its incarnation is stamped as in the native State, with the epoch
        // as the transaction component: {block, epoch} by the prologue or
        // transaction that created or re-created the account, {block,
        // LAST_TX} by create_account_no_rollback, and {0, 0} for an account
        // decoded from the witness, which no stamp can equal. It drives
        // is_current_incarnation, EIP-6780, the storage clearing on
        // re-creation, and whether commit starts the storage from empty.
        std::optional<Account> account_{};
    };

    // The AccountState of every address this block has touched. A segmented
    // map so that rows never move once created, which lets the journal and
    // the slot maps hold pointers to them; keyed by the seeded address hash
    // (see key_hash.hpp). Consecutive lookups repeat an address far more
    // often than not, so the last row found is kept and a 20-byte compare
    // answers the repeat without a hash or probe.
    class AccountStateMap
    {
        KeySeed const &seed_;
        ankerl::unordered_dense::segmented_map<
            Address, AccountState, AddressHash>
            map_;
        Address last_address_{};
        AccountState *last_{nullptr};

    public:
        // `floor` rows are reserved up front: the guest's arena never
        // frees, so growth is a copy and a leak.
        AccountStateMap(KeySeed const &seed, size_t const floor)
            : seed_{seed}
            , map_{floor, AddressHash{seed}}
        {
        }

        struct Found
        {
            AccountState &account_state;
            bool inserted;
        };

        // The row for `address`, created from the seed if absent.
        [[nodiscard]] [[gnu::always_inline]] inline Found
        find_or_emplace(Address const &address)
        {
            if (last_ != nullptr && address == last_address_) {
                return {*last_, false};
            }
            auto const [it, inserted] = map_.try_emplace(address, seed_);
            last_address_ = address;
            last_ = &it->second;
            return {it->second, inserted};
        }

        [[nodiscard]] size_t size() const noexcept
        {
            return map_.size();
        }

        [[nodiscard]] auto begin() noexcept
        {
            return map_.begin();
        }

        [[nodiscard]] auto end() noexcept
        {
            return map_.end();
        }

        [[nodiscard]] auto begin() const noexcept
        {
            return map_.begin();
        }

        [[nodiscard]] auto end() const noexcept
        {
            return map_.end();
        }
    };

}

MONAD_NAMESPACE_END
