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
    /// is recorded as `last_mutated` on every facet/slot whose value actually
    /// changed (see `StorageDelta::last_mutated` and the per-field stamps on
    /// `StateDelta`). Non-transaction merges (block prologue/epilogue, RPC
    /// state overrides) use `LAST_MUTATED_NONE`.
    ///
    /// Returns whether this merge destroyed a storage-bearing contract — a
    /// committed account with non-NULL code going to nullopt. That is the one
    /// event that wipes a storage namespace out from under the per-slot stamps,
    /// so it is the case the simplified conflict model cannot see; it is
    /// surfaced purely as an observation signal to gauge the noise. It is ~zero
    /// on Monad (EIP-6780 restricts SELFDESTRUCT to same-transaction creates).
    bool merge(State const &, uint64_t txn_index = LAST_MUTATED_NONE);

    /// Per-axis "last conflict index" for a transaction (parallel-gas
    /// experiment): for each facet the transaction *read* — is_alive
    /// (existence/empty, as observed by CALL new-account gas and EXTCODEHASH),
    /// balance, nonce, code, and storage slots — the greatest `last_mutated`
    /// over the keys it read on that axis. That is the block index of the most
    /// recent earlier transaction it read-after-write conflicts with on that
    /// axis; `LAST_MUTATED_NONE` means no in-block conflict there. The read set
    /// is the per-facet read mask on each `OriginalAccountState` (balance reuses
    /// `validate_exact_balance`); storage reads are the slots present in its
    /// `storage_`. `overall()` is the max across all axes.
    ///
    /// The transaction's own `sender` nonce is excluded: it is preloaded to
    /// `tx.nonce` (`set_original_nonce`), a consensus-known value the executor
    /// never has to read from a predecessor, so a same-sender nonce ordering is
    /// not a real parallelization dependency. The beneficiary is *not* excluded:
    /// its priority-fee credit is applied in `execute_final` (after the read set
    /// is taken) via a commutative `add_to_balance`, so it never enters the read
    /// set; only genuine reads of the beneficiary count.
    ///
    /// Intended to be called at the transaction's in-order merge point, so that
    /// every `last_mutated` it observes belongs to an earlier transaction.
    struct ConflictIndex
    {
        uint64_t is_alive = LAST_MUTATED_NONE;
        uint64_t balance = LAST_MUTATED_NONE;
        uint64_t nonce = LAST_MUTATED_NONE;
        uint64_t code = LAST_MUTATED_NONE;
        uint64_t storage = LAST_MUTATED_NONE;

        [[nodiscard]] uint64_t overall() const
        {
            uint64_t j = LAST_MUTATED_NONE;
            for (uint64_t const v :
                 {is_alive, balance, nonce, code, storage}) {
                if (v != LAST_MUTATED_NONE &&
                    (j == LAST_MUTATED_NONE || v > j)) {
                    j = v;
                }
            }
            return j;
        }
    };

    ConflictIndex
    last_conflict_index(State const &, Address const &sender = {}) const;

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
