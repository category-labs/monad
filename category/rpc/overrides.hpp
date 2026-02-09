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

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <optional>

struct monad_state_override
{
    struct monad_state_override_object
    {
        std::optional<monad::uint256_t> balance{std::nullopt};
        std::optional<uint64_t> nonce{std::nullopt};
        std::optional<monad::byte_string> code{std::nullopt};
        ankerl::unordered_dense::segmented_map<
            monad::bytes32_t, monad::bytes32_t>
            state{};
        ankerl::unordered_dense::segmented_map<
            monad::bytes32_t, monad::bytes32_t>
            state_diff{};
    };

    ankerl::unordered_dense::segmented_map<
        monad::Address, monad_state_override_object>
        override_sets;
};

struct monad_block_override
{
    std::optional<uint64_t> number{std::nullopt};
    std::optional<uint64_t> time{std::nullopt};
    std::optional<uint64_t> gas_limit{std::nullopt};
    std::optional<monad::Address> fee_recipient{std::nullopt};
    std::optional<monad::bytes32_t> prev_randao{std::nullopt};
    std::optional<monad::uint256_t> base_fee_per_gas{std::nullopt};
    std::optional<monad::uint256_t> blob_base_fee{std::nullopt};
};
