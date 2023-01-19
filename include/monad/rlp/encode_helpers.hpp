#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/encode.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

struct Account;

MONAD_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string encode_unsigned(unsigned_integral auto const &n)
{
    return encode_string(to_big_compact(n));
}

inline byte_string encode_bytes32(bytes32_t const &b)
{
    return encode_string(to_byte_string_view(b.bytes));
}

inline byte_string encode_address(address_t const &a)
{
    return encode_string(to_byte_string_view(a.bytes));
}

byte_string encode_account(Account const &, bytes32_t const &code_root);

MONAD_RLP_NAMESPACE_END
