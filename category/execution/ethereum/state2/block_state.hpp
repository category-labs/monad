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
    // Optional cross-check db: when non-null, every storage read is also
    // performed against this db and the result asserted to match. Used by
    // the dual-db migration path to detect divergence between the slot-
    // encoded primary and the page-encoded secondary.
    Db *secondary_db_;
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
    // multi-block cache: when tracking, reads memoize consensus stamps and
    // merge() collects the per-transaction stamp candidates in commit order
    bool const stamp_tracking_;
    uint64_t block_number_{0};
    uint64_t account_boundary_{0};
    uint64_t storage_boundary_{0};
    BlockStampCandidates stamp_candidates_;

public:
    BlockState(
        Db &, vm::VM &, Db *secondary_db = nullptr,
        bool stamp_tracking = false);

    vm::VM &vm()
    {
        return vm_;
    }

    bool stamp_tracking() const
    {
        return stamp_tracking_;
    }

    uint64_t block_number() const
    {
        return block_number_;
    }

    uint64_t account_boundary() const
    {
        return account_boundary_;
    }

    uint64_t storage_boundary() const
    {
        return storage_boundary_;
    }

    // window boundaries as of the parent block: warm iff stamp != 0 and
    // stamp >= boundary
    void set_pricing_window(
        uint64_t const block_number, uint64_t const account_boundary,
        uint64_t const storage_boundary)
    {
        block_number_ = block_number;
        account_boundary_ = account_boundary;
        storage_boundary_ = storage_boundary;
    }

    std::optional<Account>
    read_account(Address const &, uint64_t *stamp = nullptr);

    bytes32_t read_storage(
        Address const &, Incarnation, bytes32_t const &key,
        uint64_t *stamp = nullptr);

    vm::SharedVarcode read_code(bytes32_t const &);

    bool can_merge(State &) const;

    void merge(State const &);

    struct ReleasedState
    {
        std::unique_ptr<StateDeltas> state;
        Code code;
        SelfDestructStorageReads self_destruct_storage_reads;
        BlockStampCandidates stamp_candidates;
    };

    ReleasedState release() &&;

    void log_debug();
};

MONAD_NAMESPACE_END
