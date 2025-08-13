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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/core/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_access_list(AccessList const &);
byte_string encode_transaction(Transaction const &);
byte_string encode_transaction_for_signing(Transaction const &);

Result<std::vector<bytes32_t>> decode_access_entry_keys(byte_string_view &);
Result<AccessEntry> decode_access_entry(byte_string_view &);
Result<AccessList> decode_access_list(byte_string_view &);

Result<Transaction> decode_transaction_legacy(byte_string_view &);
Result<Transaction> decode_transaction_eip2718(byte_string_view &);
Result<Transaction> decode_transaction(byte_string_view &);
Result<std::vector<Transaction>> decode_transaction_list(byte_string_view &enc);

MONAD_RLP_NAMESPACE_END
