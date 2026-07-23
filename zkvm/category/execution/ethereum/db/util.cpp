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

// zkVM replacement for category/execution/ethereum/db/util.cpp. The host TU
// is dropped from the guest build because it pulls in the whole category/mpt
// machinery and nlohmann/json. commit_builder.cpp (kept in the guest) only
// needs the two RLP account/storage encoders, reproduced here verbatim.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>

MONAD_NAMESPACE_BEGIN

byte_string encode_account_db(Address const &address, Account const &account)
{
    byte_string encoded_account;
    encoded_account += rlp::encode_address(address);
    encoded_account += rlp::encode_unsigned(account.incarnation.to_int());
    encoded_account += rlp::encode_unsigned(account.nonce);
    encoded_account += rlp::encode_unsigned(account.balance);
    if (account.code_hash != NULL_HASH) {
        encoded_account += rlp::encode_bytes32(account.code_hash);
    }
    return rlp::encode_list2(encoded_account);
}

byte_string encode_storage_db(bytes32_t const &key, bytes32_t const &val)
{
    byte_string encoded_storage;
    encoded_storage += rlp::encode_bytes32_compact(key);
    encoded_storage += rlp::encode_bytes32_compact(val);
    return rlp::encode_list2(encoded_storage);
}

MONAD_NAMESPACE_END
