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

#pragma once

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

namespace monad::vm::runtime
{
    template <Traits traits>
    void log_impl(
        Context *ctx, uint256_t const &offset_word, uint256_t const &size_word,
        std::span<evmc::bytes32 const> topics);

    template <Traits traits>
    void
    log0(Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr);

    template <Traits traits>
    void log1(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr);

    template <Traits traits>
    void log2(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr, uint256_t const *topic2_ptr);

    template <Traits traits>
    void log3(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr, uint256_t const *topic2_ptr,
        uint256_t const *topic3_ptr);

    template <Traits traits>
    void log4(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr, uint256_t const *topic2_ptr,
        uint256_t const *topic3_ptr, uint256_t const *topic4_ptr);
}
