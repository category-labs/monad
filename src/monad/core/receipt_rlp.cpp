#include <monad/core/address_rlp.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_rlp.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/receipt_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode2.hpp>

#include <cstddef>
#include <cstdint>
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
        return encode_string2(
            static_cast<unsigned char>(receipt.type) + receipt_bytes);
    }
    return receipt_bytes;
}

// Decode
byte_string_view decode_bloom(Receipt::Bloom &bloom, byte_string_view const enc)
{
    return decode_byte_array<256>(bloom.data(), enc);
}

byte_string_view
decode_topics(std::vector<bytes32_t> &topics, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    constexpr size_t topic_size =
        33; // 1 byte for header, 32 bytes for byte32_t
    auto const list_space = payload.size();
    MONAD_ASSERT(topics.size() == 0);
    topics.reserve(list_space / topic_size);

    while (payload.size() > 0) {
        bytes32_t topic{};
        payload = decode_bytes32(topic, payload);
        topics.emplace_back(topic);
    }

    MONAD_ASSERT(list_space == topics.size() * topic_size);
    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_log(Receipt::Log &log, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    payload = decode_address(log.address, payload);
    payload = decode_topics(log.topics, payload);
    payload = decode_string(log.data, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_logs(std::vector<Receipt::Log> &logs, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    constexpr size_t approx_data_size = 32;
    constexpr size_t approx_num_topics = 10;
    // 20 bytes for address, 33 bytes per topic
    constexpr auto log_size_approx =
        20 + approx_data_size + 33 * approx_num_topics;
    auto const list_space = payload.size();
    MONAD_ASSERT(logs.size() == 0);
    logs.resize(list_space / log_size_approx);

    while (payload.size() > 0) {
        Receipt::Log log{};
        payload = decode_log(log, payload);
        logs.emplace_back(log);
    }

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view
decode_untyped_receipt(Receipt &receipt, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);
    payload = decode_unsigned<uint64_t>(receipt.status, payload);
    payload = decode_unsigned<uint64_t>(receipt.gas_used, payload);
    payload = decode_bloom(receipt.bloom, payload);
    payload = decode_logs(receipt.logs, payload);

    MONAD_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_receipt(Receipt &receipt, byte_string_view const enc)
{
    MONAD_ASSERT(enc.size() > 0);

    uint8_t const &first = enc[0];
    receipt.type = TransactionType::eip155;
    if (first < 0xc0) // eip 2718 - typed transaction envelope
    {
        byte_string_view payload{};
        auto const rest_of_enc = parse_string_metadata(payload, enc);
        MONAD_ASSERT(payload.size() > 0);

        uint8_t const &type = payload[0];
        auto const receipt_enc = payload.substr(1, payload.size() - 1);
        switch (type) {
        case 0x1:
            receipt.type = TransactionType::eip2930;
            break;
        case 0x2:
            receipt.type = TransactionType::eip1559;
            break;
        default:
            MONAD_ASSERT(false); // invalid transaction type
            return {};
        }
        auto const rest_of_receipt_enc =
            decode_untyped_receipt(receipt, receipt_enc);
        MONAD_ASSERT(rest_of_receipt_enc.size() == 0);
        return rest_of_enc;
    }
    return decode_untyped_receipt(receipt, enc);
}

MONAD_RLP_NAMESPACE_END
