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
#include "fuzzer_view.hpp"

#include <category/core/assert.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <ranges>
#include <span>

namespace monad::vm::fuzzing
{
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

    void assert_states_equal(SortedStateView const &a, SortedStateView const &b)
    {
        MONAD_ASSERT(a.size() == b.size());

        for (auto const &[a_acc, b_acc] : std::views::zip(a, b)) {
            MONAD_ASSERT(a_acc.addr == b_acc.addr);
            MONAD_ASSERT(a_acc.nonce == b_acc.nonce);
            MONAD_ASSERT(a_acc.balance == b_acc.balance);
            MONAD_ASSERT(a_acc.code_hash == b_acc.code_hash);
            MONAD_ASSERT(std::ranges::equal(a_acc.code, b_acc.code));

            auto const a_st = a.storage(a_acc.addr);
            auto const b_st = b.storage(b_acc.addr);

            MONAD_ASSERT(a_st->size() == b_st->size());

            for (auto const &[a_se, b_se] : std::views::zip(*a_st, *b_st)) {
                MONAD_ASSERT(a_se.key == b_se.key);
                MONAD_ASSERT(a_se.current == b_se.current);
                MONAD_ASSERT(a_se.original == b_se.original);
                MONAD_ASSERT(a_se.access_status == b_se.access_status);
            }

            auto const a_ts = a.transient_storage(a_acc.addr);
            auto const b_ts = b.transient_storage(b_acc.addr);

            MONAD_ASSERT(a_ts->size() == b_ts->size());

            for (auto const &[a_te, b_te] : std::views::zip(*a_ts, *b_ts)) {
                MONAD_ASSERT(a_te.key == b_te.key);
                MONAD_ASSERT(a_te.value == b_te.value);
            }
        }
    }

    void
    assert_backend_states_equal(FuzzerBackend const &a, FuzzerBackend const &b)
    {
        auto const a_view = a.sorted_view();
        auto const b_view = b.sorted_view();
        assert_states_equal(*a_view, *b_view);
    }
}
