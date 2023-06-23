#pragma once

#include <ethash/keccak.hpp>

#include <monad/rlp/config.hpp>
#include <monad/rlp/encode.hpp>
#include <monad/rlp/util.hpp>

#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/trie/config.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct Account;

MONAD_NAMESPACE_END

MONAD_TRIE_NAMESPACE_BEGIN

struct Leaf;
struct Branch;

MONAD_TRIE_NAMESPACE_END

MONAD_RLP_NAMESPACE_BEGIN

inline byte_string const EMPTY_STRING = {0x80};

inline byte_string encode_unsigned(unsigned_integral auto const &n)
{
    return encode_string(to_big_compact(n));
}

inline byte_string encode_bytes32(bytes32_t const &b)
{
    return encode_string(to_byte_string_view(b.bytes));
}

inline byte_string encode_address(std::optional<address_t> const &a)
{
    if (!a.has_value()) {
        return byte_string({0x80});
    }
    return encode_string(to_byte_string_view(a->bytes));
}

byte_string encode_account(Account const &, bytes32_t const &storage_root);
byte_string encode_transaction(Transaction const &);
byte_string encode_transaction_for_signing(Transaction const &);
byte_string encode_access_list(Transaction::AccessList const &list);
byte_string encode_topics(std::vector<bytes32_t> const &topics);
byte_string encode_log(Receipt::Log const &log);
byte_string encode_bloom(Receipt::Bloom const &b);
byte_string encode_receipt(Receipt const &receipt);

byte_string encode_leaf(trie::Leaf const &);
byte_string encode_branch(trie::Branch const &);
byte_string to_node_reference(byte_string_view rlp);

MONAD_RLP_NAMESPACE_END
