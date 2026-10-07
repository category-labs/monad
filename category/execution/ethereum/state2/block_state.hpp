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
    // Optional cross-check db: when non-null, every storage read is also
    // performed against this db and the result asserted to match. Used by
    // the dual-db migration path to detect divergence between the slot-
    // encoded primary and the page-encoded secondary.
    Db *secondary_db_;
    vm::VM &vm_;
    std::unique_ptr<StateDeltas> state_;
    Code code_;
    /// Preserve pre-state storage reads for the witness when creation or
    /// deletion clears an account's storage delta. Capture them only on the
    /// first reset: later reads refer to storage created within this block.
    SelfDestructStorageReads self_destruct_storage_reads_;

public:
    BlockState(Db &, vm::VM &, Db *secondary_db = nullptr);

    vm::VM &vm()
    {
        return vm_;
    }

    std::optional<Account> read_account(Address const &);

    bytes32_t read_storage(Address const &, bytes32_t const &key);

    // Full RPC storage replacement; call only between executions.
    void clear_storage(Address const &);

    vm::SharedVarcode read_code(bytes32_t const &);

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
