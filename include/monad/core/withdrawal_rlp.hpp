#pragma once

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_withdrawal(Withdrawal const &withdrawal);

byte_string_view
decode_withdrawal(Withdrawal &withdrawal, byte_string_view const enc);
byte_string_view decode_withdrawal_list(
    std::vector<Withdrawal> &withdrawal_list, byte_string_view const enc);

MONAD_RLP_NAMESPACE_END
