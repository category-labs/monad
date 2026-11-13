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

// The zkVM guest's state backend: one State per block, built from the
// witness, satisfying the same StateInterface as the native state3 State.
//
// Where the native stack keeps a per-transaction State over a BlockState over
// a Db, the guest keeps a single row per address for the whole block.
// Transaction scope is an epoch stamp on the row rather than a copy of it,
// reverts are an undo journal, and every keccak is computed once and kept
// where it is needed again. Nothing here is shared with the production
// client beyond the interface header.
//
// Rows, witness reads, writes, warmth, the journal, the transaction boundary
// and commit are in place.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/state3/state_interface.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/access_status.hpp>
#include <category/vm/evm/page_storage_status.hpp>
#include <category/vm/evm/storage_status.hpp>
#include <category/vm/vm.hpp>
#include <zkvm/state/account_state.hpp>
#include <zkvm/state/journal.hpp>
#include <zkvm/state/key_hash.hpp>
#include <zkvm/state/slot_map.hpp>

#include <ankerl/unordered_dense.h>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace zkvm
{
    class State : public StateBase<State>
    {
        friend class StateBase<State>;

    public:
        using CodeTable = ankerl::unordered_dense::segmented_map<
            bytes32_t, vm::SharedVarcode, Bytes32Hash>;

    private:
        // Keys every map and index of this State; see key_hash.hpp.
        KeySeed const seed_;
        // The witness, pre-state and post-state alike: commit writes the
        // overlay and state_root() hashes it.
        mpt::OffsetTrie trie_;
        // Every code the witness carries plus what this block deploys, by
        // hash. Rows point into it, so it is never shrunk. NULL_HASH maps to
        // the empty code from construction. Built by the driver with the
        // same seed, which the constructor asserts.
        CodeTable codes_;
        // The table's NULL_HASH entry, which get_code hands out for an
        // absent account without a probe.
        vm::SharedVarcode const *empty_code_{nullptr};
        vm::VM &vm_;

        AccountStateMap accounts_;

        uint64_t const block_number_;
        // 0 during the block prologue, i + 1 while transaction i runs. Bumped
        // rather than set to the transaction index so rows touched in the
        // prologue begin a new epoch in the first transaction as well.
        uint64_t epoch_{0};
        // Every AccountState that began the current epoch, walked by
        // destruct_suicides and destruct_touched_dead and cleared by
        // begin_transaction.
        std::vector<AccountState *> epoch_account_states_;
        // Frames, undo records and logs; see journal.hpp.
        Journal journal_;

        // The row for an address: begins the epoch if its own is stale, and on
        // first use created by resolve_account.
        AccountState &account_state_for(Address const &);
        // Hash the address and walk the account trie once, recording the
        // resolution, the leaf and the storage root and seeding `account`
        // from the decoded leaf.
        void resolve_account(Address const &, AccountState &);
        // The slot row for a key: begins the epoch if its own is stale, and
        // created on first use without touching the trie.
        SlotState &slot(AccountState &, bytes32_t const &key);
        // Start the current epoch on an AccountState: reset its
        // transaction-scoped fields, stamp the epoch and record it in
        // epoch_account_states_.
        void begin_epoch(AccountState &);
        // The row's account for a write, materialised with this
        // transaction's stamp (and journalled) if absent.
        Account &ensure_account(AccountState &);

        // The storage half of commit for a surviving account: upserts and
        // erases every written slot whose post-state value differs from the
        // witness, threading the storage sub-root through `storage`. True if
        // anything was written.
        bool commit_storage(AccountState &, mpt::NodeId &storage);

        // The stamp for accounts the current transaction creates. The guest
        // never persists it, so the epoch serves as the transaction
        // component: it is only ever compared for equality within this
        // block, and a witness account's {0, 0} matches no stamp.
        Incarnation incarnation() const
        {
            return Incarnation{block_number_, epoch_};
        }

        // StateBase primitives. recent_account aborts on an unproven
        // account: the witness cannot say whether it exists.
        std::optional<Account> const &recent_account(Address const &);

        // The account's code through the row's cache, resolving from the
        // code table only when the hash it was resolved for has changed.
        vm::SharedVarcode const &code_of(AccountState &, Account const &);

        // EIP-2929 slot warmth. MIP-8 does not apply to the guest, so the
        // `page` instantiation aborts; it exists because StateHost names it
        // under a constexpr branch no EVM revision takes.
        template <bool page>
        AccessStatus access_storage_impl(Address const &, bytes32_t const &key);

        template <SelfdestructRule rule>
        std::pair<bool, uint256_t>
        selfdestruct_impl(Address const &, Address const &beneficiary);

        template <SelfdestructRule rule>
        void destruct_suicides_impl();

    public:
        // `seed` keys every table; the driver derives it from the block hash
        // with KeySeed::from_block_hash and builds the CodeTable with it.
        State(
            mpt::OffsetTrie, CodeTable, vm::VM &, uint64_t block_number,
            KeySeed const &seed);

        State(State &&) = delete;
        State(State const &) = delete;
        State &operator=(State &&) = delete;
        State &operator=(State const &) = delete;

        ////////////////////////////////////////
        // Block lifecycle, guest-only

        // Start transaction `i`, which must follow transaction i - 1 (or the
        // prologue for i == 0): the epoch becomes i + 1. No frame may be
        // open and the logs must have been taken.
        void begin_transaction(uint64_t i);

        // Hand the transaction's logs to its receipt.
        std::vector<Receipt::Log> take_logs();

        // Write every row with `written` set to the trie overlay: the
        // accounts the post-state holds first, the deleted ones after.
        void commit();

        // The root of the trie as it stands: the witness's pre-state root
        // until commit, the post-state root after.
        bytes32_t state_root();

        ////////////////////////////////////////
        // StateInterface

        void push();

        void pop_accept();

        void pop_reject();

        vm::VM &vm();

        // account_exists, account_is_dead, account_has_code_or_nonce, get_nonce
        // and get_code_hash come from StateBase.

        uint256_t get_balance(Address const &);

        bool is_destructed(Address const &);

        bool is_current_incarnation(Address const &);

        bool is_touched(Address const &);

        void set_nonce(Address const &, uint64_t nonce);

        void add_to_balance(Address const &, uint256_t const &delta);

        void subtract_from_balance(Address const &, uint256_t const &delta);

        void touch(Address const &);

        void create_contract(Address const &);

        void create_account_no_rollback(Address const &);

        void set_to_state_incarnation(Address const &);

        // destruct_suicides<traits> comes from StateBase and dispatches to
        // destruct_suicides_impl.

        void destruct_touched_dead();

        bytes32_t get_storage(Address const &, bytes32_t const &key);

        // Guest-only, outside the StateInterface: get_storage for a caller
        // that can live without the answer. Nullopt when the witness proves
        // neither the slot's value nor its absence, where get_storage
        // aborts. The guest's EIP-2935 read (block_hash_history_impl.cpp)
        // uses it to fall back to the header chain.
        std::optional<bytes32_t>
        try_get_storage(Address const &, bytes32_t const &key);

        StorageStatus set_storage(
            Address const &, bytes32_t const &key, bytes32_t const &value);

        bytes32_t get_transient_storage(Address const &, bytes32_t const &key);

        void set_transient_storage(
            Address const &, bytes32_t const &key, bytes32_t const &value);

        AccessStatus access_account(Address const &);

        // access_storage<traits> comes from StateBase and dispatches to
        // access_storage_impl.

        PageStorageStatus
        update_page(Address const &, bytes32_t const &key, StorageStatus);

        vm::SharedVarcode read_code(bytes32_t const &code_hash);

        vm::SharedVarcode get_code(Address const &);

        size_t get_code_size(Address const &);

        size_t copy_code(
            Address const &, size_t offset, uint8_t *buffer,
            size_t buffer_size);

        void set_code(Address const &, byte_string_view code);

        std::span<Receipt::Log const> logs();

        void store_log(Receipt::Log const &);

        // There is no speculative merge in the guest: a plain balance check.
        bool record_balance_constraint_for_debit(
            Address const &, uint256_t const &debit);
    };

    static_assert(StateInterface<State>);
}

MONAD_NAMESPACE_END
