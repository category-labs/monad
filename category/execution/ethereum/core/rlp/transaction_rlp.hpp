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
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_access_list(AccessList const &);
byte_string encode_authorization_entry_for_signing(AuthorizationEntry const &);
byte_string encode_transaction(Transaction const &);
byte_string encode_transaction_for_signing(Transaction const &);

Result<std::vector<bytes32_t>> decode_access_entry_keys(byte_string_view &);
Result<AccessEntry> decode_access_entry(byte_string_view &);
Result<AccessList> decode_access_list(byte_string_view &);

Result<AuthorizationEntry> decode_authorization_entry(byte_string_view &);
Result<AuthorizationList> decode_authorization_list(byte_string_view &);

Result<Transaction> decode_transaction_legacy(byte_string_view &);
Result<Transaction> decode_transaction_eip2718(byte_string_view &);
Result<Transaction> decode_transaction(byte_string_view &);
Result<std::vector<Transaction>> decode_transaction_list(byte_string_view &enc);

// As above, and if `raw` is non-null, appends to it the exact byte slice each
// transaction was decoded from -- for a legacy transaction the list with its
// header, for a typed one the unwrapped `type | payload`. Those are precisely
// the values the transactions trie holds, so a caller that keeps them can
// check the header's transactions_root against the bytes it decoded rather
// than against its own re-encoding of what it decoded.
//
// The slices point into `enc`; nothing here copies, and the caller owns that
// buffer's lifetime.
Result<std::vector<Transaction>>
decode_transaction_list(byte_string_view &enc, std::vector<byte_string_view> *raw);

MONAD_RLP_NAMESPACE_END
