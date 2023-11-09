#include <monad/core/address_rlp.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int_rlp.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_withdrawal(Withdrawal const &withdrawal)
{
    return encode_list(
        encode_unsigned(withdrawal.index),
        encode_unsigned(withdrawal.validator_index),
        encode_address(withdrawal.recipient),
        encode_unsigned(withdrawal.amount));
}

byte_string_view
decode_withdrawal(Withdrawal &withdrawal, byte_string_view const enc)
{
    if (enc.size() == 0) {
        return {};
    }
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    payload = decode_unsigned<uint64_t>(withdrawal.index, payload);
    payload = decode_unsigned<uint64_t>(withdrawal.validator_index, payload);
    payload = decode_address(withdrawal.recipient, payload);
    payload = decode_unsigned<uint64_t>(withdrawal.amount, payload);

    MONAD_DEBUG_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

byte_string_view decode_withdrawal_list(
    std::vector<Withdrawal> &withdrawal_list, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_list_metadata(payload, enc);

    withdrawal_list.reserve(payload.size() / sizeof(Withdrawal));

    while (payload.size() > 0) {
        Withdrawal withdrawal{};
        payload = decode_withdrawal(withdrawal, payload);
        withdrawal_list.emplace_back(withdrawal);
    }

    MONAD_DEBUG_ASSERT(payload.size() == 0);
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
