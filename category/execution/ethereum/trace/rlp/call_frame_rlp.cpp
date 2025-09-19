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
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>

#include <boost/outcome/try.hpp>

#include <span>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_call_frame(CallFrame const &call_frame)
{
    return encode_list2(
        encode_unsigned(static_cast<unsigned char>(call_frame.type)),
        encode_unsigned(call_frame.flags),
        encode_address(call_frame.from),
        encode_address(call_frame.to),
        encode_unsigned(call_frame.value),
        encode_unsigned(call_frame.gas),
        encode_unsigned(call_frame.gas_used),
        encode_string2(call_frame.input),
        encode_string2(call_frame.output),
        encode_unsigned(static_cast<unsigned char>(call_frame.status)),
        encode_unsigned(call_frame.depth));
}

byte_string encode_call_frames(std::span<CallFrame const> const call_frames)
{
    byte_string res{};
    for (auto const &call_frame : call_frames) {
        res += encode_call_frame(call_frame);
    }

    return encode_list2(res);
}

Result<CallFrame> decode_call_frame(byte_string_view &enc)
{
    CallFrame call_frame{};
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(auto const type, decode_unsigned<unsigned char>(payload));
    call_frame.type = static_cast<enum CallType>(type);
    BOOST_OUTCOME_TRY(call_frame.flags, decode_unsigned<uint32_t>(payload));
    BOOST_OUTCOME_TRY(call_frame.from, decode_address(payload));
    BOOST_OUTCOME_TRY(call_frame.to, decode_optional_address(payload));
    BOOST_OUTCOME_TRY(call_frame.value, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(call_frame.gas, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(call_frame.gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(call_frame.input, decode_string(payload));
    BOOST_OUTCOME_TRY(call_frame.output, decode_string(payload));
    BOOST_OUTCOME_TRY(
        auto const status, decode_unsigned<unsigned char>(payload));
    call_frame.status = static_cast<enum evmc_status_code>(status);
    BOOST_OUTCOME_TRY(call_frame.depth, decode_unsigned<uint64_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return call_frame;
}

Result<std::vector<CallFrame>> decode_call_frames(byte_string_view &enc)
{
    std::vector<CallFrame> call_frames;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto call_frame, decode_call_frame(payload));
        call_frames.emplace_back(std::move(call_frame));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return call_frames;
}

MONAD_RLP_NAMESPACE_END
