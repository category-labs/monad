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

#include <category/core/runtime/uint256.hpp>

#include <evmc/evmc.hpp>

#include <cstdint>

namespace monad::vm::utils::evm_as::sugar
{
    // Convenience structures for writing call instructions with named and
    // default arguments.
    struct CallArgs
    {
        uint64_t const gas{0};
        evmc::address const address{0};
        runtime::uint256_t const value{0};
        runtime::uint256_t const args_offset{0};
        runtime::uint256_t const args_size{0};
        runtime::uint256_t const ret_offset{0};
        runtime::uint256_t const ret_size{0};
    };

    struct CallCodeArgs
    {
        uint64_t const gas{0};
        evmc::address const address{0};
        runtime::uint256_t const value{0};
        runtime::uint256_t const args_offset{0};
        runtime::uint256_t const args_size{0};
        runtime::uint256_t const ret_offset{0};
        runtime::uint256_t const ret_size{0};
    };

    struct DelegateCallArgs
    {
        uint64_t const gas{0};
        evmc::address const address{0};
        runtime::uint256_t const args_offset{0};
        runtime::uint256_t const args_size{0};
        runtime::uint256_t const ret_offset{0};
        runtime::uint256_t const ret_size{0};
    };

    struct StaticCallArgs
    {
        uint64_t const gas{0};
        evmc::address const address{0};
        runtime::uint256_t const args_offset{0};
        runtime::uint256_t const args_size{0};
        runtime::uint256_t const ret_offset{0};
        runtime::uint256_t const ret_size{0};
    };
}
