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

#include <category/core/config.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/staking/read_valset.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

MONAD_NAMESPACE_BEGIN

monad_validator_set
monad_read_valset(mpt::Db &db, size_t const block_num, bool get_next)
{
    vm::VM vm;
    TrieDb tdb(db);
    BlockState block_state{tdb, vm};
    Incarnation const incarnation{block_num, Incarnation::LAST_TX - 1u};
    State state{block_state, incarnation};
    staking::StakingContract contract(state);
    state.add_to_balance(staking::STAKING_CA, 0);

    if (!contract.vars.in_epoch_delay_period.load()) {
        get_next = false;
    }
    auto const valset = get_next ? contract.vars.valset_consensus
                                 : contract.vars.valset_snapshot;
    auto get_stake = [&](u64_be const id) {
        return get_next ? contract.vars.consensus_stake(id)
                        : contract.vars.snapshot_stake(id);
    };

    uint64_t const length = valset.length();
    auto output = monad_alloc_valset(length);

    for (uint64_t i = 0; i < length; i += 1) {
        auto const val_id = valset.get(i).load();
        auto const stake = get_stake(val_id).load();
        auto const keys = contract.vars.val_execution(val_id).keys().load();
        std::memcpy(output.valset[i].secp_pubkey, keys.secp_pubkey.data(), 33);
        std::memcpy(output.valset[i].bls_pubkey, keys.bls_pubkey.data(), 48);
        std::memcpy(output.valset[i].stake.bytes, stake.bytes, 32);
    }
    return output;
}

MONAD_NAMESPACE_END
