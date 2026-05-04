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

#include <category/core/assert.h>
#include <category/execution/ethereum/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <span>
#include <unordered_map>

namespace monad::vm::fuzzing
{
    void assert_equal(
        AccountState::StorageMap const &a, AccountState::StorageMap const &b)
    {
        MONAD_ASSERT(a.size() == b.size());
        for (auto const &[k, v] : a) {
            auto const *found = b.find(k);
            MONAD_ASSERT(found != nullptr);
            MONAD_ASSERT(*found == v);
        }
    }

    void assert_equal(
        Address const &k, State &a, AccountState const &as, State &b,
        AccountState const &bs)
    {
        MONAD_ASSERT(a.account_exists(k) == b.account_exists(k));
        MONAD_ASSERT(a.get_nonce(k) == b.get_nonce(k));
        MONAD_ASSERT(a.account_is_dead(k) == b.account_is_dead(k));
        MONAD_ASSERT(a.get_balance(k) == b.get_balance(k));
        MONAD_ASSERT(a.get_original_balance(k) == b.get_original_balance(k));
        MONAD_ASSERT(a.get_code_hash(k) == b.get_code_hash(k));
        MONAD_ASSERT(a.is_destructed(k) == b.is_destructed(k));
        MONAD_ASSERT(
            a.is_current_incarnation(k) == b.is_current_incarnation(k));
        MONAD_ASSERT(a.is_touched(k) == b.is_touched(k));

        assert_equal(as.storage_, bs.storage_);
        assert_equal(as.transient_storage_, bs.transient_storage_);
        MONAD_ASSERT(as.get_accessed_storage() == bs.get_accessed_storage());
    }

    void assert_equal(State &a, State &b)
    {
        MONAD_ASSERT(a.current().size() == b.current().size());

        // Deep copy to prevent mutation of the given account maps:
        std::unordered_map<Address, AccountState> a_accs;
        for (auto const &[k, v] : a.current()) {
            MONAD_ASSERT(v.size() == 1);
            auto const [_, is_new] = a_accs.insert({k, v.recent()});
            MONAD_ASSERT(is_new);
        }
        std::unordered_map<Address, AccountState> b_accs;
        for (auto const &[k, v] : b.current()) {
            MONAD_ASSERT(v.size() == 1);
            auto const [_, is_new] = b_accs.insert({k, v.recent()});
            MONAD_ASSERT(is_new);
        }

        for (auto const &[k, v] : a_accs) {
            auto const found = b_accs.find(k);
            MONAD_ASSERT(found != b_accs.end());
            assert_equal(k, a, v, b, found->second);
        }
    }

    void assert_equal(
        evmc::Result const &evmone_result, evmc::Result const &compiler_result,
        bool const strict_out_of_gas)
    {
        MONAD_ASSERT(std::ranges::equal(
            evmone_result.create_address.bytes,
            compiler_result.create_address.bytes));

        MONAD_ASSERT(evmone_result.gas_left == compiler_result.gas_left);
        MONAD_ASSERT(evmone_result.gas_refund == compiler_result.gas_refund);

        MONAD_ASSERT(std::ranges::equal(
            std::span(evmone_result.output_data, evmone_result.output_size),
            std::span(
                compiler_result.output_data, compiler_result.output_size)));

        switch (evmone_result.status_code) {
        case EVMC_SUCCESS:
        case EVMC_REVERT:
            MONAD_ASSERT(
                evmone_result.status_code == compiler_result.status_code);
            break;
        case EVMC_OUT_OF_GAS: {
            if (strict_out_of_gas) {
                MONAD_ASSERT(compiler_result.status_code == EVMC_OUT_OF_GAS);
            }
            else {
                // For the compiler, we allow a relaxed check for out-of-gas,
                // where it is permitted to resolve to either a generic failure
                // *or* an out-of-gas failure. This is because the compiler may
                // statically produce a generic error for code that would
                // dynamically run out of gas.
                MONAD_ASSERT(
                    compiler_result.status_code == EVMC_OUT_OF_GAS ||
                    compiler_result.status_code == EVMC_FAILURE);
            }
            break;
        }
        default:
            MONAD_ASSERT(compiler_result.status_code != EVMC_SUCCESS);
            MONAD_ASSERT(compiler_result.status_code != EVMC_REVERT);
            break;
        }
    }

}
