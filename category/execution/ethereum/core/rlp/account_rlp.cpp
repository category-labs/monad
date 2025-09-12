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
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/execution/ethereum/rlp/decode_error.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>

MONAD_RLP_NAMESPACE_BEGIN

byte_string
encode_account(Account const &account, bytes32_t const &storage_root)
{
    return encode_list2(
        encode_unsigned(account.nonce),
        encode_unsigned(account.balance),
        encode_bytes32(storage_root),
        encode_bytes32(account.get_code_hash()));
}

Result<Account> decode_account(bytes32_t &storage_root, byte_string_view &enc)
{
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    Account acct;
    BOOST_OUTCOME_TRY(acct.nonce, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(acct.balance, decode_unsigned<uint256_t>(payload));
    BOOST_OUTCOME_TRY(storage_root, decode_bytes32(payload));
    BOOST_OUTCOME_TRY(acct.code_or_hash, decode_bytes32(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return acct;
}

MONAD_RLP_NAMESPACE_END
