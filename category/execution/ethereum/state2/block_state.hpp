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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
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

public:
    BlockState(Db &, vm::VM &);

    vm::VM &vm()
    {
        return vm_;
    }

    std::optional<Account> read_account(evmc_address const &);

    bytes32_t
    read_storage(evmc_address const &, Incarnation, bytes32_t const &key);

#ifdef MONAD_ZKVM_ZISK
    // Find or load the account entry. Its pointer stays valid for the block:
    // segmented storage preserves pointers on insert, and entries are not erased.
    StateDelta &read_account_delta(evmc_address const &);

    // Read using the supplied delta, without copying the returned slot value.
    // The reference points into block storage, or to a static zero value;
    // use it before that slot is modified or erased.
    bytes32_t const &read_storage(
        StateDelta &, evmc_address const &, Incarnation, bytes32_t const &key);
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
