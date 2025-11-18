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

#include "account.hpp"
#include "hash_utils.hpp"
#include "state.hpp"
#include "test_state.hpp"

#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/vm/core/assert.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <span>
#include <iostream>

using namespace evmone::state;

namespace monad::vm::fuzzing
{
    void assert_equal(StorageValue const &a, StorageValue const &b)
    {
        MONAD_VM_ASSERT(a.current == b.current);
        MONAD_VM_ASSERT(a.original == b.original);
        MONAD_VM_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(evmone::state::Account const &a, evmone::state::Account const &b)
    {
        MONAD_VM_ASSERT(
            a.transient_storage.size() == b.transient_storage.size());
        for (auto const &[k, v] : a.transient_storage) {
            auto const found = b.transient_storage.find(k);
            MONAD_VM_ASSERT(found != b.transient_storage.end());
            MONAD_VM_ASSERT(found->second == v);
        }

        MONAD_VM_ASSERT(a.storage.size() == b.storage.size());
        for (auto const &[k, v] : a.storage) {
            auto const found = b.storage.find(k);
            MONAD_VM_ASSERT(found != b.storage.end());
            assert_equal(v, found->second);
        }

        MONAD_VM_ASSERT(a.nonce == b.nonce);
        MONAD_VM_ASSERT(a.balance == b.balance);
        MONAD_VM_ASSERT(a.code_hash == b.code_hash);
        MONAD_VM_ASSERT(a.destructed == b.destructed);
        MONAD_VM_ASSERT(a.erase_if_empty == b.erase_if_empty);
        MONAD_VM_ASSERT(a.just_created == b.just_created);
        MONAD_VM_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(evmone::state::State const &a, evmone::state::State const &b)
    {
        auto const &a_accs = a.get_modified_accounts();
        auto const &b_accs = b.get_modified_accounts();

        MONAD_VM_ASSERT(a_accs.size() == b_accs.size());
        for (auto const &[k, v] : a_accs) {
            auto const found = b_accs.find(k);
            MONAD_VM_ASSERT(found != b_accs.end());
            assert_equal(v, found->second);
        }
    }

    void assert_equal(evmone::test::TestState const &evmone, monad::BlockState &monad)
    {
        // TODO we don't check for size of both states so the monadstate could potentially contain more?
        for (auto const& [addr, acc] : evmone)
        {
            std::cerr << "checking " << evmc::hex(addr) << std::endl;
            auto const macc = monad.read_account(addr);

            MONAD_VM_ASSERT(!!macc);
                            std::cerr << std::format("acc.balance: {} macc.balance: {}\n", hex(acc.balance), hex(macc->balance));

            MONAD_VM_ASSERT(macc->balance == acc.balance);
            MONAD_VM_ASSERT(macc->nonce == acc.nonce);
            MONAD_VM_ASSERT(macc->code_hash == evmone::keccak256(acc.code));

            auto incarnation = macc->incarnation;
            for (auto const& [k, v] : acc.storage)
            {
                MONAD_VM_ASSERT(monad.read_storage(addr, incarnation, k) == v);
            }
        }
    }
    

    void assert_equal(StateDiff::Entry const &a, StateDiff::Entry const &b)
    {
        MONAD_VM_ASSERT(a.addr == b.addr);
        MONAD_VM_ASSERT(a.nonce == b.nonce);
        MONAD_VM_ASSERT(a.balance == b.balance);

        // Compare optional code
        MONAD_VM_ASSERT(a.code.has_value() == b.code.has_value());
        if (a.code && b.code){
            MONAD_VM_ASSERT(*a.code == *b.code);
        }
        // Compare modified storage
        MONAD_VM_ASSERT(a.modified_storage.size() == b.modified_storage.size());
        for (size_t i = 0; i < a.modified_storage.size(); ++i)
        {
            auto const& [key_a, val_a] = a.modified_storage[i];
            auto const& [key_b, val_b] = b.modified_storage[i];
            MONAD_VM_ASSERT(key_a == key_b);
            MONAD_VM_ASSERT(val_a == val_b);
        }
    }


    void assert_equal(StateDiff::Entry const &a, StateView::Account const &b)
    {
        MONAD_VM_ASSERT(a.modified_storage.size() == 0);
        MONAD_VM_ASSERT(a.nonce == b.nonce);
        MONAD_VM_ASSERT(a.balance == b.balance);

        // Compare optional code hash
        if (a.code){
            MONAD_VM_ASSERT(evmone::keccak256(*a.code) == b.code_hash);
        }
    }


     void assert_equal_deleted_accounts(std::vector<address> const& a, std::vector<address> const& b, evmone::test::TestState const &initial)
    {
        if(a.size() < b.size()) return assert_equal_deleted_accounts(b, a, initial);
        for (auto const& addr_a : a)
        {
            auto it = std::find(b.begin(), b.end(), addr_a);
            if(it == b.end()){
                auto initial_b = initial.get_account(addr_a);
                MONAD_VM_ASSERT(!initial_b);
            }
        }
    }


    void assert_equal(StateDiff const& a, StateDiff const& b, evmone::test::TestState const &initial)
    {
        if(a.modified_accounts.size() < b.modified_accounts.size()) return assert_equal(b, a, initial);
        // Compare modified_accounts
        // MONAD_VM_ASSERT(a.modified_accounts.size() == b.modified_accounts.size());

        for (auto const& entry_a : a.modified_accounts)
        {
            auto it = std::find_if(b.modified_accounts.begin(), b.modified_accounts.end(),
                                [&](auto const& e) { return e.addr == entry_a.addr; });
            // MONAD_VM_ASSERT(it != b.modified_accounts.end());
            if (it != b.modified_accounts.end())
            {
                assert_equal(entry_a, *it);
            }
            else
            {
                auto const initial_b = initial.get_account(entry_a.addr);
                
                MONAD_VM_ASSERT(!!initial_b);
                assert_equal(entry_a, *initial_b);
            }
        }

        // Compare deleted_accounts
        assert_equal_deleted_accounts(a.deleted_accounts, b.deleted_accounts, initial);
    }

    void assert_equal(
        evmc::Result const &evmone_result, evmc::Result const &compiler_result,
        bool const strict_out_of_gas)
    {
        MONAD_VM_ASSERT(std::ranges::equal(
            evmone_result.create_address.bytes,
            compiler_result.create_address.bytes));

        MONAD_VM_ASSERT(evmone_result.gas_left == compiler_result.gas_left);
        MONAD_VM_ASSERT(evmone_result.gas_refund == compiler_result.gas_refund);

        MONAD_VM_ASSERT(std::ranges::equal(
            std::span(evmone_result.output_data, evmone_result.output_size),
            std::span(
                compiler_result.output_data, compiler_result.output_size)));

        switch (evmone_result.status_code) {
        case EVMC_SUCCESS:
        case EVMC_REVERT:
            MONAD_VM_ASSERT(
                evmone_result.status_code == compiler_result.status_code);
            break;
        case EVMC_OUT_OF_GAS: {
            if (strict_out_of_gas) {
                MONAD_VM_ASSERT(compiler_result.status_code == EVMC_OUT_OF_GAS);
            }
            else {
                // For the compiler, we allow a relaxed check for out-of-gas,
                // where it is permitted to resolve to either a generic failure
                // *or* an out-of-gas failure. This is because the compiler may
                // statically produce a generic error for code that would
                // dynamically run out of gas.
                MONAD_VM_ASSERT(
                    compiler_result.status_code == EVMC_OUT_OF_GAS ||
                    compiler_result.status_code == EVMC_FAILURE);
            }
            break;
        }
        default:
            MONAD_VM_ASSERT(compiler_result.status_code != EVMC_SUCCESS);
            MONAD_VM_ASSERT(compiler_result.status_code != EVMC_REVERT);
            break;
        }
    }

    void assert_equal(
        evmone::state::TransactionReceipt const &evmone_result, evmone::state::TransactionReceipt const &compiler_result,
        evmone::test::TestState const &initial, bool const strict_out_of_gas)
    {
        MONAD_VM_ASSERT(evmone_result.gas_used == compiler_result.gas_used);

        switch (evmone_result.status) {
        case EVMC_SUCCESS:
        case EVMC_REVERT:
            MONAD_VM_ASSERT(
                evmone_result.status == compiler_result.status);
            break;
        case EVMC_OUT_OF_GAS: {
            if (strict_out_of_gas) {
                MONAD_VM_ASSERT(compiler_result.status == EVMC_OUT_OF_GAS);
            }
            else {
                // For the compiler, we allow a relaxed check for out-of-gas,
                // where it is permitted to resolve to either a generic failure
                // *or* an out-of-gas failure. This is because the compiler may
                // statically produce a generic error for code that would
                // dynamically run out of gas.
                MONAD_VM_ASSERT(
                    compiler_result.status == EVMC_OUT_OF_GAS ||
                    compiler_result.status == EVMC_FAILURE);
            }
            break;
        }
        default:
            MONAD_VM_ASSERT(compiler_result.status != EVMC_SUCCESS);
            MONAD_VM_ASSERT(compiler_result.status != EVMC_REVERT);
            break;
        }

        assert_equal(evmone_result.state_diff, compiler_result.state_diff, initial);
    }

}
