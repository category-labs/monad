#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>

MONAD_RLP_NAMESPACE_BEGIN

template <unsigned_integral T>
inline constexpr byte_string_view
decode_unsigned(T &u_num, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    u_num = decode_raw_num<T>(payload);
    return rest_of_enc;
}

inline byte_string_view
decode_bytes32(bytes32_t &bytes, byte_string_view const enc)
{
    return decode_byte_array<32>(bytes.bytes, enc);
}

inline byte_string_view
decode_address(address_t &address, byte_string_view const enc)
{
    return decode_byte_array<20>(address.bytes, enc);
}

byte_string_view
decode_account(Account &acc, bytes32_t &code_root, byte_string_view const enc);

MONAD_RLP_NAMESPACE_END
