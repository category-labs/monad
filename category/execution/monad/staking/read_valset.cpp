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

MONAD_STAKING_NAMESPACE_BEGIN

std::optional<std::vector<Validator>>
read_valset(mpt::Db &db, size_t const block_num, uint64_t const requested_epoch)
{
    vm::VM vm;
    TrieDb tdb{db};
    tdb.set_block_and_prefix(block_num);
    BlockState block_state{tdb, vm};
    Incarnation const incarnation{block_num, Incarnation::LAST_TX - 1u};
    State state{block_state, incarnation};
    staking::StakingContract contract(state);
    state.add_to_balance(staking::STAKING_CA, 0);

    uint64_t const contract_epoch = contract.vars.epoch.load().native();
    if (requested_epoch == contract_epoch + 1) {
        if (!contract.vars.in_epoch_delay_period.load()) {
            // can't read the next epoch before the boundary block.
            return std::nullopt;
        }
    }
    if (requested_epoch < contract_epoch) {
        // old epoch which no longer exists
        return std::nullopt;
    }
    if (requested_epoch > contract_epoch + 1) {
        // hasn't happened yet
        return std::nullopt;
    }

    bool const get_next_epoch = requested_epoch == (contract_epoch + 1);
    auto const contract_valset = get_next_epoch
                                     ? contract.vars.valset_consensus
                                     : contract.vars.this_epoch_valset();
    auto get_stake = [&](u64_be const id) {
        return get_next_epoch ? contract.vars.consensus_view(id).stake()
                              : contract.vars.this_epoch_view(id).stake();
    };

    uint64_t const length = contract_valset.length();
    MONAD_ASSERT(length <= ACTIVE_VALSET_SIZE)
    std::vector<Validator> valset(length);
    for (uint64_t i = 0; i < length; i += 1) {
        auto const val_id = contract_valset.get(i).load();
        auto const stake = get_stake(val_id).load();
        auto const keys = contract.vars.val_execution(val_id).keys().load();
        std::memcpy(valset[i].secp_pubkey, keys.secp_pubkey.data(), 33);
        std::memcpy(valset[i].bls_pubkey, keys.bls_pubkey.data(), 48);
        std::memcpy(valset[i].stake.bytes, stake.bytes, 32);
    }
    return valset;
}

MONAD_STAKING_NAMESPACE_END
