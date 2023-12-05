#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/receipt.hpp>
#include <monad/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_topics(std::vector<bytes32_t> const &);
byte_string encode_log(Receipt::Log const &);
byte_string encode_bloom(Receipt::Bloom const &);
byte_string encode_receipt(Receipt const &);

decode_result_t decode_bloom(Receipt::Bloom &, byte_string_view);
decode_result_t decode_topics(std::vector<bytes32_t> &, byte_string_view);
decode_result_t decode_log(Receipt::Log &, byte_string_view);
decode_result_t decode_logs(std::vector<Receipt::Log> &, byte_string_view);
decode_result_t decode_receipt(Receipt &, byte_string_view);

MONAD_RLP_NAMESPACE_END
