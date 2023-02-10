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

// glee for shea: not sure how to incorporate `unsigned_integral` concept...
// -------------------------------------------------------------------------
// glee for glee: we should remove the template default and require explicit
//                typing to avoid unnecessary stack allocation (smaller num).
// glee: Removed template default for reason stated above.
template <typename T>
inline T decode_unsigned(byte_string_view const enc, byte_string_loc &i)
{
    const auto dec = decode_string(enc, i);
    return decode_num<T>(dec, 0, dec.size());
}

// Do these functions need to be written here?
bytes32_t decode_bytes32(byte_string_view const enc, byte_string_loc &i);
address_t decode_address(byte_string_view const enc, byte_string_loc &i);
SignatureAndChain decode_sc(byte_string_view const enc, byte_string_loc &i);

Receipt::Bloom decode_bloom(byte_string_view const enc, byte_string_loc& i);
byte_string decode_log_data(byte_string_view enc, byte_string_loc& i);
std::vector<bytes32_t> decode_topics(byte_string_view enc, byte_string_loc& i);
Receipt::Log decode_log(byte_string_view enc, byte_string_loc& i);
std::vector<Receipt::Log> decode_logs(byte_string_view const enc, byte_string_loc& i);

std::vector<bytes32_t> decode_access_entry_keys(byte_string_view const enc, byte_string_loc &i);
Transaction::AccessEntry decode_access_entry(byte_string_view const enc, byte_string_loc &i);
Transaction::AccessList decode_access_list(byte_string_view const enc, byte_string_loc &i);
std::pair<Account, bytes32_t> decode_account(byte_string_view const enc, byte_string_loc &i);
Transaction decode_transaction(byte_string_view const enc, byte_string_loc &i);
Receipt decode_receipt(byte_string_view const enc, byte_string_loc& i);

Block decode_block(byte_string const enc);

MONAD_RLP_NAMESPACE_END
