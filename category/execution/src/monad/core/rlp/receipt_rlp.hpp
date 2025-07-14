#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <monad/core/receipt.hpp>
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
