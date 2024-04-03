#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/int_rlp.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <utility>
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

Result<Withdrawal> decode_withdrawal(byte_string_view &enc)
{
    Withdrawal withdrawal;
    if (enc.size() == 0) {
        return withdrawal;
    }
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    BOOST_OUTCOME_TRY(withdrawal.index, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(
        withdrawal.validator_index, decode_unsigned<uint64_t>(payload));
    BOOST_OUTCOME_TRY(withdrawal.recipient, decode_address(payload));
    BOOST_OUTCOME_TRY(withdrawal.amount, decode_unsigned<uint64_t>(payload));

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return withdrawal;
}

Result<std::vector<Withdrawal>> decode_withdrawal_list(byte_string_view &enc)
{
    std::vector<Withdrawal> withdrawal_list;
    BOOST_OUTCOME_TRY(auto payload, parse_list_metadata(enc));
    withdrawal_list.reserve(payload.size() / sizeof(Withdrawal));

    while (payload.size() > 0) {
        BOOST_OUTCOME_TRY(auto withdrawal, decode_withdrawal(payload));
        withdrawal_list.emplace_back(std::move(withdrawal));
    }

    if (MONAD_UNLIKELY(!payload.empty())) {
        return DecodeError::InputTooLong;
    }

    return withdrawal_list;
}

MONAD_RLP_NAMESPACE_END
