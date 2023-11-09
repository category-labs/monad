#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/encode.hpp>

#include <optional>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_address(std::optional<address_t> const &address)
{
    if (!address.has_value()) {
        return byte_string({0x80});
    }
    return encode_string(to_byte_string_view(address->bytes));
}

inline byte_string_view
decode_address(address_t &address, byte_string_view const enc)
{
    return decode_byte_array<20>(address.bytes, enc);
}

inline byte_string_view
decode_address(std::optional<address_t> &address, byte_string_view const enc)
{
    byte_string_view payload{};
    auto const rest_of_enc = parse_string_metadata(payload, enc);
    if (payload.size() == sizeof(address_t)) {
        address = address_t{};
        std::memcpy(address->bytes, payload.data(), sizeof(address_t));
    }
    else {
        MONAD_ASSERT(payload.size() == 0);
        address.reset();
    }
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
