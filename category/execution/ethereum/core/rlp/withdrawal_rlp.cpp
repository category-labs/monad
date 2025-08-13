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
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <utility>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_withdrawal(Withdrawal const &withdrawal)
{
    return encode_list2(
        encode_unsigned(withdrawal.index),
        encode_unsigned(withdrawal.validator_index),
        encode_address(withdrawal.recipient),
        encode_unsigned(withdrawal.amount));
}

Result<Withdrawal> decode_withdrawal(byte_string_view &enc)
{
    Withdrawal withdrawal;
    if (enc.size() == 0) {
        return withdrawal;
    }
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(withdrawal.index, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        withdrawal.validator_index, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(withdrawal.recipient, decode_address(payload));
    BOOST_OUTCOME_TRY(withdrawal.amount, decode_unsigned<uint64_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return withdrawal;
}

Result<std::vector<Withdrawal>> decode_withdrawal_list(byte_string_view &enc)
{
    std::vector<Withdrawal> withdrawal_list;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    withdrawal_list.reserve(payload.size() / sizeof(Withdrawal));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto withdrawal, decode_withdrawal(payload));
        withdrawal_list.emplace_back(std::move(withdrawal));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return withdrawal_list;
}

MONAD_RLP_NAMESPACE_END
