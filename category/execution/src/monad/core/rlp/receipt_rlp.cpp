#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/rlp/receipt_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

// Encode
byte_string encode_topics(std::vector<bytes32_t> const &topics)
{
    byte_string result{};
    for (auto const &i : topics) {
        result += encode_bytes32(i);
    }
    return encode_list2(result);
}

byte_string encode_log(Receipt::Log const &log)
{
    return encode_list2(
        encode_address(log.address),
        encode_topics(log.topics),
        encode_string2(log.data));
}

byte_string encode_bloom(Receipt::Bloom const &bloom)
{
    return encode_string2(to_byte_string_view(bloom));
}

byte_string encode_receipt(Receipt const &receipt)
{
    byte_string log_result{};

    for (auto const &i : receipt.logs) {
        log_result += encode_log(i);
    }

    auto const receipt_bytes = encode_list2(
        encode_unsigned(receipt.status),
        encode_unsigned(receipt.gas_used),
        encode_bloom(receipt.bloom),
        encode_list2(log_result));

    if (receipt.type == TransactionType::eip1559 ||
        receipt.type == TransactionType::eip2930) {
        return static_cast<unsigned char>(receipt.type) + receipt_bytes;
    }
    return receipt_bytes;
}

// Decode
Result<Receipt::Bloom> decode_bloom(byte_string_view &enc)
{
    return decode_byte_string_fixed<256>(enc);
}

Result<std::vector<bytes32_t>> decode_topics(byte_string_view &enc)
{
    std::vector<bytes32_t> topics;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    constexpr size_t topic_size =
        33; // 1 byte for header, 32 bytes for byte32_t
    auto const list_space = payload.size();
    topics.reserve(list_space / topic_size);

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto topic, decode_bytes32(payload));
        topics.emplace_back(std::move(topic));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return topics;
}

Result<Receipt::Log> decode_log(byte_string_view &enc)
{
    Receipt::Log log;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(log.address, decode_address(payload));
    BOOST_OUTCOME_TRY(log.topics, decode_topics(payload));
    BOOST_OUTCOME_TRY(log.data, decode_string(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return log;
}

Result<std::vector<Receipt::Log>> decode_logs(byte_string_view &enc)
{
    std::vector<Receipt::Log> logs;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto log, decode_log(payload));
        logs.emplace_back(std::move(log));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return logs;
}

Result<Receipt> decode_untyped_receipt(byte_string_view &enc)
{
    Receipt receipt;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(receipt.status, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(receipt.gas_used, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(receipt.bloom, decode_bloom(payload));
    BOOST_OUTCOME_TRY(receipt.logs, decode_logs(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return receipt;
}

Result<Receipt> decode_receipt(byte_string_view &enc)
{
    if (MONAD_UNLIKELY(enc.empty())) {
        return DecodeError::InputTooShort;
    }

    Receipt receipt;

    unsigned char const first = enc[0];
    if (first < 0xc0) // eip 2718 - typed transaction envelope
    {
        enc = enc.substr(1);
        BOOST_OUTCOME_TRY(receipt, decode_untyped_receipt(enc));
        switch (first) {
        case 0x1:
            receipt.type = TransactionType::eip2930;
            break;
        case 0x2:
            receipt.type = TransactionType::eip1559;
            break;
        default:
            return DecodeError::InvalidTxnType;
        }

        return receipt;
    }
    else {
        BOOST_OUTCOME_TRY(receipt, decode_untyped_receipt(enc));
        receipt.type = TransactionType::legacy;

        return receipt;
    }
}

MONAD_RLP_NAMESPACE_END
