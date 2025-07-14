#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/result.hpp>
#include <category/core/rlp/config.hpp>
#include <monad/core/withdrawal.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_withdrawal(Withdrawal const &);

Result<Withdrawal> decode_withdrawal(byte_string_view &);
Result<std::vector<Withdrawal>> decode_withdrawal_list(byte_string_view &);

MONAD_RLP_NAMESPACE_END
