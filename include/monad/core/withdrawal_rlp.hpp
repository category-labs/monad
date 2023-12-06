#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/result.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_withdrawal(Withdrawal const &);

Result<byte_string_view> decode_withdrawal(Withdrawal &, byte_string_view);
Result<byte_string_view>
decode_withdrawal_list(std::vector<Withdrawal> &, byte_string_view);

MONAD_RLP_NAMESPACE_END
