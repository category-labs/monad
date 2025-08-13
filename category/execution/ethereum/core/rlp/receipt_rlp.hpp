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
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_topics(std::vector<bytes32_t> const &);
byte_string encode_log(Receipt::Log const &);
byte_string encode_bloom(Receipt::Bloom const &);
byte_string encode_receipt(Receipt const &);

Result<Receipt::Bloom> decode_bloom(byte_string_view &);
Result<std::vector<bytes32_t>> decode_topics(byte_string_view &);
Result<Receipt::Log> decode_log(byte_string_view &);
Result<std::vector<Receipt::Log>> decode_logs(byte_string_view &);
Result<Receipt> decode_receipt(byte_string_view &);

MONAD_RLP_NAMESPACE_END
