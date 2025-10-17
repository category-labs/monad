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

#include "assertions.hpp"
#include "account.hpp"
#include "state.hpp"

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
        FUZZER_ASSERT(a.current == b.current);
        FUZZER_ASSERT(a.original == b.original);
        FUZZER_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(Account const &a, Account const &b)
    {
        FUZZER_ASSERT(a.transient_storage.size() == b.transient_storage.size());
        for (auto const &[k, v] : a.transient_storage) {
            auto const found = b.transient_storage.find(k);
            FUZZER_ASSERT(found != b.transient_storage.end());
            FUZZER_ASSERT(found->second == v);
        }

        FUZZER_ASSERT(a.storage.size() == b.storage.size());
        for (auto const &[k, v] : a.storage) {
            auto const found = b.storage.find(k);
            FUZZER_ASSERT(found != b.storage.end());
            assert_equal(v, found->second);
        }

        FUZZER_ASSERT(a.nonce == b.nonce);
        FUZZER_ASSERT(a.balance == b.balance);
        FUZZER_ASSERT(a.code_hash == b.code_hash);
        FUZZER_ASSERT(a.destructed == b.destructed);
        FUZZER_ASSERT(a.erase_if_empty == b.erase_if_empty);
        FUZZER_ASSERT(a.just_created == b.just_created);
        FUZZER_ASSERT(a.access_status == b.access_status);
    }

    void assert_equal(State const &a, State const &b)
    {
        auto const &a_accs = a.get_modified_accounts();
        auto const &b_accs = b.get_modified_accounts();

        FUZZER_ASSERT(a_accs.size() == b_accs.size());
        for (auto const &[k, v] : a_accs) {
            auto const found = b_accs.find(k);
            FUZZER_ASSERT(found != b_accs.end());
            assert_equal(v, found->second);
        }
    }

    void assert_equal(
        evmc::Result const &evmone_result, evmc::Result const &compiler_result,
        bool const strict_out_of_gas)
    {
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
    std::cerr << std::format("expected status:{} actual status:{}\n", (int)evmone_result.status_code, (int)compiler_result.status_code);

            break;
        }

        FUZZER_ASSERT(std::ranges::equal(
            evmone_result.create_address.bytes,
            compiler_result.create_address.bytes));

    if (evmone_result.gas_left != compiler_result.gas_left) {
        std::cerr << std::format("gas_left expected: {} actual: {}\n", evmone_result.gas_left, compiler_result.gas_left);
    }
        FUZZER_ASSERT(evmone_result.gas_left == compiler_result.gas_left);
        FUZZER_ASSERT(evmone_result.gas_refund == compiler_result.gas_refund);

        FUZZER_ASSERT(std::ranges::equal(
            std::span(evmone_result.output_data, evmone_result.output_size),
            std::span(
                compiler_result.output_data, compiler_result.output_size)));

    }

}
