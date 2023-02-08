#pragma once

#include <monad/rlp/config.hpp>
#include <monad/rlp/decode.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

MONAD_NAMESPACE_BEGIN

struct Account;

MONAD_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

std::pair<Account, bytes32_t> decode_account(byte_string const enc);
Block decode_block(byte_string const enc);

MONAD_RLP_NAMESPACE_END
