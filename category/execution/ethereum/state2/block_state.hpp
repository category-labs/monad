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

    std::optional<Account> read_account(Address const &);

    bytes32_t read_storage(Address const &, Incarnation, bytes32_t const &key);

    vm::SharedVarcode read_code(bytes32_t const &);

    bool can_merge(State &) const;

    /// Merge a transaction's accumulated writes into the block state.
    /// `txn_index` is the block-relative index of the merging transaction; it
    /// is recorded as `last_mutated` on every write-touched key (see
    /// `StorageDelta::last_mutated`). Non-transaction merges (block
    /// prologue/epilogue, RPC state overrides) use `LAST_MUTATED_NONE`.
    void merge(State const &, uint64_t txn_index = LAST_MUTATED_NONE);

    /// Prototype (parallel-gas experiment): compute the "last conflict index"
    /// `j` for a transaction — the greatest `last_mutated` over the keys in the
    /// transaction's read set, i.e. the block index of the most recent earlier
    /// transaction it conflicts with (read-after-write). Returns
    /// `LAST_MUTATED_NONE` if the read set intersects no in-block write.
    ///
    /// `beneficiary` is excluded from the read set. EIP-3651 pre-warms the block
    /// beneficiary into every transaction's read set, and the priority-fee
    /// credit is a commutative balance add — neither is a real data dependency,
    /// so counting it would collapse the block into a `j == i-1` chain.
    ///
    /// Deliberately standalone (not folded into `can_merge`) for now. Intended
    /// to be called at the transaction's in-order merge point, so that every
    /// `last_mutated` it observes belongs to an earlier transaction.
    uint64_t
    last_conflict_index(State const &, Address const &beneficiary = {}) const;

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
