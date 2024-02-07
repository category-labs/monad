#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_withdrawal(Withdrawal const &);

Result<Withdrawal> decode_withdrawal(byte_string_view &);
Result<std::vector<Withdrawal>> decode_withdrawal_list(byte_string_view &);

MONAD_RLP_NAMESPACE_END
