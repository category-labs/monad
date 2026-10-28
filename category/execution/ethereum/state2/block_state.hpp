// Copyright (C) 2025 Category Labs, Inc.
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
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;

using SelfDestructStorageReads = ankerl::unordered_dense::segmented_map<
    Address, ankerl::unordered_dense::segmented_set<bytes32_t>>;

class BlockState final
{
    Db &db_;
    vm::VM &vm_;
    std::unique_ptr<StateDeltas> state_;
    Code code_;
    /// Storage slot reads done against a pre-state account before it got
    /// SELFDESTRUCTed in the same block. `merge()` clears
    /// `state_deltas[addr].storage` for destroyed accounts, which would
    /// erase these entries from the witness access set.
    ///
    /// Populated at most once per address — on the *first* SELFDESTRUCT
    /// — and only when the address had an account in pre-state. Later
    /// destructs in the same block can only target a within-block
    /// incarnation (which, by definition, has no pre-state storage), so
    /// the slots they wipe are not pre-state reads and must not be added.
    SelfDestructStorageReads self_destruct_storage_reads_;

#ifdef MONAD_ZKVM_ZISK
    // Accumulate fees until the beneficiary is read or the block is finalized.
    // Alignment keeps address comparisons efficient on ZisK.
    alignas(8) Address beneficiary_{};
    uint256_t pending_beneficiary_credit_{};
    // The incarnation an absent beneficiary is created with: that of the
    // first transaction whose fee is pending, which would have created it.
    Incarnation first_credit_incarnation_{0, 0};
    bool has_pending_beneficiary_credit_{false};
    bool beneficiary_deferral_enabled_{false};

    // Adds the pending fees to the beneficiary's entry and clears them.
    [[gnu::noinline, gnu::cold]] void apply_beneficiary_credit(StateDelta &);
#endif

public:
    BlockState(Db &, vm::VM &);

    vm::VM &vm()
    {
        return vm_;
    }

    std::optional<Account> read_account(monad_address const &);

    bytes32_t
    read_storage(monad_address const &, Incarnation, bytes32_t const &key);

#ifdef MONAD_ZKVM_ZISK
    // Find or load the account and apply any pending beneficiary fees.
    // Its pointer stays valid for the block:
    // segmented storage preserves pointers on insert, and entries are not
    // erased.
    StateDelta &read_account_delta(monad_address const &);

    // Read using the supplied delta, without copying the returned slot value.
    // The reference points into block storage, or to a static zero value;
    // use it before that slot is modified or erased.
    bytes32_t const &read_storage(
        StateDelta &, monad_address const &, Incarnation, bytes32_t const &key);

    // The beneficiary whose fees defer_beneficiary_credit holds back. Set
    // once, by the sequential block loop, before its first transaction.
    void set_beneficiary(Address const &beneficiary)
    {
        MONAD_ASSERT(!has_pending_beneficiary_credit_);
        beneficiary_ = beneficiary;
        beneficiary_deferral_enabled_ = true;
    }

    bool beneficiary_deferral_enabled() const
    {
        return beneficiary_deferral_enabled_;
    }

    Address const &beneficiary() const
    {
        return beneficiary_;
    }

    // A transaction's fee to the beneficiary, credited when its entry is
    // next read or at flush_beneficiary_credit, whichever comes first. The
    // incarnation is the transaction's, for an account that does not exist.
    void defer_beneficiary_credit(uint256_t const &, Incarnation);

    // Credits whatever is pending: the block's state is complete only after.
    void flush_beneficiary_credit();
#endif

    vm::SharedVarcode read_code(bytes32_t const &);

#if defined(MONAD_ZKVM_VARCODE_CACHE)
    // Borrow the cached shared_ptr; the VM must outlive the reference.
    vm::SharedVarcode const &read_code_ref(bytes32_t const &);
#endif

    bool can_merge(State &) const;

    void merge(State const &);

    struct ReleasedState
    {
        std::unique_ptr<StateDeltas> state;
        Code code;
        SelfDestructStorageReads self_destruct_storage_reads;
    };

    ReleasedState release() &&;

    void log_debug();
};

MONAD_NAMESPACE_END
