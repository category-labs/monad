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

#include <category/vm/evm/delegation.hpp>

#include <evmc/bytes.hpp>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

namespace monad::vm::evm
{
    namespace
    {
        inline constexpr std::array<uint8_t, 3>
            delegation_indicator_prefix_bytes{0xef, 0x01, 0x00};

        inline constexpr auto delegation_indicator_size =
            delegation_indicator_prefix_bytes.size() + sizeof(evmc_address);
    }

    evmc::bytes_view delegation_indicator_prefix()
    {
        return {
            delegation_indicator_prefix_bytes.data(),
            delegation_indicator_prefix_bytes.size()};
    }

    bool is_delegated(std::span<uint8_t const> code)
    {
        if (code.size() != delegation_indicator_size) {
            return false;
        }

        auto const prefix = delegation_indicator_prefix();
        return std::equal(prefix.begin(), prefix.end(), code.begin());
    }

    std::optional<evmc::address> resolve_delegation(
        evmc_host_interface const *host, evmc_host_context *ctx,
        evmc::address const &addr)
    {
        // Copy up to |code_size| bytes of the bytecode. Then test
        // whether the code begins with the prefix 0xEF0100, if so,
        // then drop these three bytes and interpret the remainder as
        // the delegate address.
        constexpr uint8_t indicator[] = {0xef, 0x01, 0x00};
        constexpr size_t indicator_size = std::size(indicator);
        constexpr size_t expected_code_size =
            indicator_size + sizeof(evmc_address);
        static_assert(expected_code_size == 23);

        uint8_t code_buffer[expected_code_size];
        auto const actual_code_size =
            host->copy_code(ctx, &addr, 0, code_buffer, expected_code_size);

        std::span const code{code_buffer, actual_code_size};
        if (!is_delegated(code)) {
            return std::nullopt;
        }

        // Copy the delegate address from the code buffer.
        evmc::address designation;
        std::ranges::copy(
            code.subspan(indicator_size, sizeof(evmc_address)),
            designation.bytes);
        return designation;
    }
}
