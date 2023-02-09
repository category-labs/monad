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

MONAD_RLP_NAMESPACE_BEGIN

inline decoding_with_updated_ptr<byte_string_loc> decode_unsigned(byte_string_view const enc, byte_string_loc i)
{
    const auto [dec, end] = decode_string(enc, i);
    return {decode_length(dec, 0, dec.size()), end};
}

std::pair<Account, bytes32_t> decode_account(byte_string_view const enc);
decoding_with_updated_ptr<Transaction> decode_transaction(byte_string_view const enc, byte_string_loc i);
Block decode_block(byte_string const enc);

MONAD_RLP_NAMESPACE_END
