#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <category/execution/ethereum/core/account.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_account(Account const &, bytes32_t const &storage_root);

Result<Account> decode_account(bytes32_t &storage_root, byte_string_view &);

MONAD_RLP_NAMESPACE_END
