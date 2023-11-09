#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/receipt.hpp>
#include <monad/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_topics(std::vector<bytes32_t> const &topics);
byte_string encode_log(Receipt::Log const &log);
byte_string encode_bloom(Receipt::Bloom const &b);
byte_string encode_receipt(Receipt const &receipt);

byte_string_view
decode_bloom(Receipt::Bloom &bloom, byte_string_view const enc);
byte_string_view
decode_topics(std::vector<bytes32_t> &topics, byte_string_view enc);
byte_string_view decode_log(Receipt::Log &log, byte_string_view enc);
byte_string_view
decode_logs(std::vector<Receipt::Log> &logs, byte_string_view const enc);
byte_string_view decode_receipt(Receipt &receipt, byte_string_view const enc);

MONAD_RLP_NAMESPACE_END
