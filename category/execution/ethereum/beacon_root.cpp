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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/beacon_root.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/state3/state.hpp>

MONAD_NAMESPACE_BEGIN

using namespace monad::literals;

void set_beacon_root(State &state, BlockHeader const &header)
{
    constexpr auto BEACON_ROOTS_ADDRESS{
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02_address};
    constexpr uint256_t HISTORY_BUFFER_LENGTH{8191};

    if (state.account_exists(BEACON_ROOTS_ADDRESS)) {
        uint256_t const timestamp{header.timestamp};
        bytes32_t const k1{
            store_be_as<bytes32_t>(timestamp % HISTORY_BUFFER_LENGTH)};
        bytes32_t const k2{store_be_as<bytes32_t>(
            timestamp % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH)};
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k1, store_be_as<bytes32_t>(timestamp));
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k2, header.parent_beacon_block_root.value());
    }
}

MONAD_NAMESPACE_END
