#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/transaction.hpp>
#include <monad/rlp/config.hpp>

#include <vector>

MONAD_RLP_NAMESPACE_BEGIN

byte_string encode_access_list(AccessList const &);
byte_string encode_transaction(Transaction const &);
byte_string encode_transaction_for_signing(Transaction const &);

byte_string_view
decode_access_entry_keys(std::vector<bytes32_t> &, byte_string_view);
byte_string_view decode_access_entry(AccessEntry &, byte_string_view);
byte_string_view decode_access_list(AccessList &, byte_string_view);
byte_string_view decode_transaction(Transaction &, byte_string_view);

MONAD_RLP_NAMESPACE_END
