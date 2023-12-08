#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/likely.h>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_error.hpp>
#include <monad/rlp/encode2.hpp>

#include <boost/outcome/try.hpp>

#include <optional>

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_address(std::optional<Address> const &address)
{
    if (!address.has_value()) {
        return byte_string({0x80});
    }
    return encode_string2(to_byte_string_view(address->bytes));
}

inline Result<byte_string_view>
decode_address(Address &address, byte_string_view const enc)
{
    return decode_byte_array<20>(address.bytes, enc);
}

inline Result<byte_string_view>
decode_address(std::optional<Address> &address, byte_string_view const enc)
{
    byte_string_view payload{};
    BOOST_OUTCOME_TRY(
        auto const rest_of_enc, parse_string_metadata(payload, enc));
    if (MONAD_LIKELY(payload.size() == sizeof(Address))) {
        address = Address{};
        std::memcpy(address->bytes, payload.data(), sizeof(Address));
    }
    else if (payload.size() > sizeof(Address)) {
        return DecodeError::InputTooLong;
    }
    else {
        if (MONAD_UNLIKELY(!payload.empty())) {
            return DecodeError::InputTooShort;
        }

        address.reset();
    }
    return rest_of_enc;
}

MONAD_RLP_NAMESPACE_END
