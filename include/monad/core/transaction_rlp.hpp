#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/transaction.hpp>
#include <monad/rlp/config.hpp>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_access_list(Transaction::AccessList const &list);
byte_string encode_transaction(Transaction const &);
byte_string encode_transaction_for_signing(Transaction const &);

byte_string_view decode_access_entry_keys(
    std::vector<bytes32_t> &keys, byte_string_view const enc);
byte_string_view
decode_access_entry(Transaction::AccessEntry &ae, byte_string_view const enc);
byte_string_view
decode_access_list(Transaction::AccessList &al, byte_string_view const enc);

byte_string_view
decode_transaction(Transaction &txn, byte_string_view const enc);

MONAD_RLP_NAMESPACE_END
