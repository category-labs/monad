#pragma once

#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/result.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_account(Account const &, bytes32_t const &storage_root);
byte_string encode_account(Account const &);

Result<Account> decode_account(bytes32_t &storage_root, byte_string_view &);
Result<Account> decode_account(byte_string_view &);

MONAD_RLP_NAMESPACE_END
