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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>

#include <gtest/gtest.h>
#include <intx/intx.hpp>

using namespace monad;
using namespace intx::literals;

TEST(Events, build_undelegation_event)
{
    // inputs for the event:
    // event Undelegate(uint64 indexed, address indexed, uint8, uint256)
    constexpr auto signature =
        0xe6a23cc8903fd274e7553a8fdd34f9683db59bbfbad485557ef86cf6fe938589_bytes32;
    u64_be const indexed_val_id = 100;
    auto const indexed_address = Address{0xdeadbeef};
    u8_be const data_withdrawal_id = 5;
    u256_be const data_amount = 1000000_u256;

    // expected outputs
    constexpr auto expected_signature = signature;
    constexpr auto expected_topic1 =
        0x0000000000000000000000000000000000000000000000000000000000000064_bytes32;
    constexpr auto expected_topic2 =
        0x00000000000000000000000000000000000000000000000000000000deadbeef_bytes32;
    byte_string const expected_data =
        evmc::from_hex(
            "0x0000000000000000000000000000000000000000000000000000000000000005"
            "00000000000000000000000000000000000000000000000000000000000f4240")
            .value();

    auto const event = EventBuilder(Address{}, signature)
                           .add_topic(abi_encode_uint(indexed_val_id))
                           .add_topic(abi_encode_address(indexed_address))
                           .add_data(abi_encode_uint(data_withdrawal_id))
                           .add_data(abi_encode_uint(data_amount))
                           .build();
    ASSERT_EQ(event.topics.size(), 3);
    EXPECT_EQ(event.topics[0], expected_signature);
    EXPECT_EQ(event.topics[1], expected_topic1);
    EXPECT_EQ(event.topics[2], expected_topic2);
    EXPECT_EQ(event.data, expected_data);
}
