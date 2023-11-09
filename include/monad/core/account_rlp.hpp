#pragma once

#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_account(Account const &, bytes32_t const &storage_root);

byte_string_view
decode_account(Account &, bytes32_t &storage_root, byte_string_view);

MONAD_RLP_NAMESPACE_END
