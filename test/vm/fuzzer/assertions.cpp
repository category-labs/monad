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
#include "assertions.hpp"
#include "state.hpp"
#include "state_predicates.hpp"

#include <category/vm/core/assert.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <span>
#include <iostream>

using namespace evmone::state;

namespace monad::vm::fuzzing
{
    // Count the number of non-empty accounts in the state.
    // Non-empty accounts are those that are not destructed and
    // not empty erasable accounts (i.e. empty accounts that
    // would be removed at the end of the transaction).
    long non_empty_accounts_size(evmc_revision const rev, std::unordered_map<address, Account> const &accs)
    {
        return std::count_if(accs.begin(), accs.end(), [rev](auto const &p) {
            return !monad::vm::fuzzing::is_account_erasable(rev, p.second);
        });
    }

    // Count the number of non-empty storage slots in the account.
    long non_empty_storage_size(std::unordered_map<bytes32, StorageValue> const &storage)
    {
        return std::count_if(storage.begin(), storage.end(), [](auto const &p) {
            return !is_storage_erasable(p.second);
        });
    }

    // Count the number of non-empty transient storage slots in the account.
    long non_empty_transient_storage_size(std::unordered_map<bytes32, bytes32> const &transient_storage)
    {
        return std::count_if(transient_storage.begin(), transient_storage.end(), [](auto const &p) {
            return !is_transient_storage_erasable(p.second);
        });
    }

    void assert_equal(StorageValue const &a, StorageValue const &b)
    {
        FUZZER_ASSERT(a.current == b.current);
        FUZZER_ASSERT(a.original == b.original);
        FUZZER_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(Account const &a, Account const &b)
    {
        FUZZER_ASSERT(
            non_empty_transient_storage_size(a.transient_storage) ==
            non_empty_transient_storage_size(b.transient_storage));
        for (auto const &[k, v] : a.transient_storage) {
            auto const found = b.transient_storage.find(k);
            if (found != b.transient_storage.end()) {
                FUZZER_ASSERT(found->second == v);
            } else {
                // Transient storage entry must be empty to be missing in b.
                FUZZER_ASSERT(is_transient_storage_erasable(v));
            }
        }

        FUZZER_ASSERT(non_empty_storage_size(a.storage) ==
                        non_empty_storage_size(b.storage));
        for (auto const &[k, v] : a.storage) {
            auto const found = b.storage.find(k);
            if (found != b.storage.end()) {
                assert_equal(v, found->second);
            } else {
                // Storage entry must be empty to be missing in b.
                FUZZER_ASSERT(is_storage_erasable(v));
            }
        }

        FUZZER_ASSERT(a.nonce == b.nonce);
        FUZZER_ASSERT(a.balance == b.balance);
        FUZZER_ASSERT(a.code_hash == b.code_hash);
        FUZZER_ASSERT(a.destructed == b.destructed);
        FUZZER_ASSERT(a.erase_if_empty == b.erase_if_empty);
        FUZZER_ASSERT(a.just_created == b.just_created);
        FUZZER_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(evmc_revision const rev, State const &a, State const &b)
    {
        auto const &a_accs = a.get_modified_accounts();
        auto const &b_accs = b.get_modified_accounts();

        FUZZER_ASSERT(non_empty_accounts_size(rev, a_accs) == non_empty_accounts_size(rev, b_accs));
        for (auto const &[k, v] : a_accs) {
            auto const found = b_accs.find(k);
            if (found != b_accs.end()) {
                if (found->second.balance != v.balance) {
                    std::cerr << "assert_equal account with address: ";
                    for (const auto& byte : k.bytes)
                        std::cerr << std::hex << static_cast<int>(byte);
                    std::cerr << std::dec << "\n";
                }
                assert_equal(v, found->second);
            } else {
                // Account must be empty and erasable to be missing in b.
                FUZZER_ASSERT(rev >= EVMC_SPURIOUS_DRAGON && v.erase_if_empty && v.is_empty());
            }
        }
    }

    void assert_equal(
        evmc::Result const &evmone_result, evmc::Result const &compiler_result,
        bool const strict_out_of_gas)
    {
        FUZZER_ASSERT(std::ranges::equal(
            evmone_result.create_address.bytes,
            compiler_result.create_address.bytes));

        FUZZER_ASSERT(evmone_result.gas_left == compiler_result.gas_left);
        FUZZER_ASSERT(evmone_result.gas_refund == compiler_result.gas_refund);

        FUZZER_ASSERT(std::ranges::equal(
            std::span(evmone_result.output_data, evmone_result.output_size),
            std::span(
                compiler_result.output_data, compiler_result.output_size)));

        switch (evmone_result.status_code) {
        case EVMC_SUCCESS:
        case EVMC_REVERT:
            FUZZER_ASSERT(
                evmone_result.status_code == compiler_result.status_code);
            break;
        case EVMC_OUT_OF_GAS: {
            if (strict_out_of_gas) {
                FUZZER_ASSERT(compiler_result.status_code == EVMC_OUT_OF_GAS);
            }
            else {
                // For the compiler, we allow a relaxed check for out-of-gas,
                // where it is permitted to resolve to either a generic failure
                // *or* an out-of-gas failure. This is because the compiler may
                // statically produce a generic error for code that would
                // dynamically run out of gas.
                FUZZER_ASSERT(
                    compiler_result.status_code == EVMC_OUT_OF_GAS ||
                    compiler_result.status_code == EVMC_FAILURE);
            }
            break;
        }
        default:
            FUZZER_ASSERT(compiler_result.status_code != EVMC_SUCCESS);
            FUZZER_ASSERT(compiler_result.status_code != EVMC_REVERT);
            break;
        }
    }

}
