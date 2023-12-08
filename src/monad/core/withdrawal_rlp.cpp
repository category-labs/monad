#include <monad/core/address_rlp.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_withdrawal(Withdrawal const &withdrawal)
{
    return encode_list2(
        encode_unsigned(withdrawal.index),
        encode_unsigned(withdrawal.validator_index),
        encode_address(withdrawal.recipient),
        encode_unsigned(withdrawal.amount));
}

Result<byte_string_view>
decode_withdrawal(Withdrawal &withdrawal, byte_string_view const enc)
{
    if (enc.size() == 0) {
        return byte_string{};
    }
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_list_metadata(payload, enc));

    BOOST_OUTCOME_TRY(
        payload, decode_unsigned<uint64_t>(withdrawal.index, payload));
    BOOST_OUTCOME_TRY(
        payload,
        decode_unsigned<uint64_t>(withdrawal.validator_index, payload));
    BOOST_OUTCOME_TRY(payload, decode_address(withdrawal.recipient, payload));
    BOOST_OUTCOME_TRY(
        payload, decode_unsigned<uint64_t>(withdrawal.amount, payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return rest_of_enc;
}

Result<byte_string_view> decode_withdrawal_list(
    std::vector<Withdrawal> &withdrawal_list, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_list_metadata(payload, enc));

    withdrawal_list.reserve(payload.size() / sizeof(Withdrawal));

    while (payload.size() > 0) {
        Withdrawal withdrawal{};
        BOOST_OUTCOME_TRY(payload, decode_withdrawal(withdrawal, payload));
        withdrawal_list.emplace_back(withdrawal);
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
