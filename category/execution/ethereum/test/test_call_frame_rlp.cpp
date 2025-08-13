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
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <vector>

using namespace monad;

namespace
{
    constexpr auto a = 0x5353535353535353535353535353535353535353_address;
    constexpr auto b = 0xbebebebebebebebebebebebebebebebebebebebe_address;
}

TEST(Rlp_CallFrame, encode_decode_call_frame)
{
    CallFrame const call_frame{
        .type = CallType::CALL,
        .flags = 1, // static call
        .from = a,
        .to = b,
        .value = 11'111u,
        .gas = 100'000u,
        .gas_used = 21'000u,
        .input = byte_string{0xaa, 0xbb, 0xcc},
        .output = byte_string{},
        .status = EVMC_SUCCESS,
        .depth = 0,
    };

    byte_string encoding = rlp::encode_call_frame(call_frame);
    byte_string_view encoding_view{encoding};
    auto const decoded_call_frame = rlp::decode_call_frame(encoding_view);
    ASSERT_FALSE(decoded_call_frame.has_error());
    EXPECT_EQ(decoded_call_frame.assume_value(), call_frame);
}

TEST(Rlp_CallFrame, encode_decode_call_frames)
{
    CallFrame const call_frame1{
        .type = CallType::CALL,
        .flags = 1, // static call
        .from = a,
        .to = b,
        .value = 11'111u,
        .gas = 100'000u,
        .gas_used = 21'000u,
        .input = byte_string{0xaa, 0xbb, 0xcc},
        .output = byte_string{},
        .status = EVMC_SUCCESS,
        .depth = 0,
    };

    CallFrame const call_frame2{
        .type = CallType::DELEGATECALL,
        .flags = 0,
        .from = b,
        .to = a,
        .value = 0,
        .gas = 10'000u,
        .gas_used = 10'000u,
        .input = byte_string{0xaa, 0xbb, 0xcc, 0xdd, 0xee, 0x01},
        .output = byte_string{0x01, 0x02},
        .status = EVMC_REVERT,
        .depth = 1,
    };

    std::vector<CallFrame> const call_frames{call_frame1, call_frame2};

    byte_string encoding = rlp::encode_call_frames(call_frames);
    byte_string_view encoding_view{encoding};
    auto const decoded_call_frames = rlp::decode_call_frames(encoding_view);
    ASSERT_FALSE(decoded_call_frames.has_error());
    ASSERT_TRUE(decoded_call_frames.assume_value().size() == 2);
    EXPECT_EQ(decoded_call_frames.assume_value()[0], call_frame1);
    EXPECT_EQ(decoded_call_frames.assume_value()[1], call_frame2);
}
