// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/vm/evm/result.hpp>
#include <category/vm/evm/status_code.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <cstdlib>

namespace monad::vm::test
{
    inline evmc::Result to_evmc_result(Result result) noexcept
    {
        auto const raw = result.release_raw();
        return evmc::Result{evmc_result{
            .status_code = to_evmc_status_code(raw.status_code),
            .gas_left = raw.gas_left,
            .gas_refund = raw.gas_refund,
            .output_data = raw.output_data,
            .output_size = raw.output_size,
            .release =
                [](evmc_result const *r) {
                    std::free(const_cast<uint8_t *>(r->output_data));
                },
            .create_address = raw.create_address,
            .padding = {},
        }};
    }

    // Copies the output, so the source's own release runs when it dies.
    inline Result from_evmc_result(evmc::Result const result) noexcept
    {
        Result out{
            from_evmc_status_code(result.status_code),
            result.gas_left,
            result.gas_refund,
            result.output_data,
            result.output_size};
        out.create_address = result.create_address;
        return out;
    }
}
