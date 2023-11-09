#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/account_rlp.hpp>
#include <monad/trie/get_trie_key_of_leaf.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/node.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

template <typename Cursor>
[[nodiscard]] std::optional<Account> trie_db_read_account(
    trie::Nibbles const &hashed_account_address, Cursor &&leaves_cursor,
    Cursor &&trie_cursor)
{
    if (MONAD_UNLIKELY(leaves_cursor.empty())) {
        return std::nullopt;
    }

    auto const [key, exists] =
        get_trie_key_of_leaf(hashed_account_address, leaves_cursor);

    if (!exists) {
        return std::nullopt;
    }

    trie_cursor.lower_bound(key);
    MONAD_ASSERT(trie_cursor.key().transform([](auto const &k) {
        return k.path();
    }) == key);

    auto const value = trie_cursor.value();
    MONAD_ASSERT(value.has_value());

    auto const node = trie::deserialize_node(key, *value);
    MONAD_ASSERT(std::holds_alternative<trie::Leaf>(node));

    Account ret;
    bytes32_t _;
    auto const rest =
        rlp::decode_account(ret, _, std::get<trie::Leaf>(node).value);
    MONAD_ASSERT(rest.empty());
    return ret;
}

template <typename Cursor>
[[nodiscard]] std::optional<Account> trie_db_read_account(
    address_t const &a, Cursor &&leaves_cursor, Cursor &&trie_cursor)
{
    auto const hashed_account_address = trie::Nibbles{
        std::bit_cast<bytes32_t>(ethash::keccak256(a.bytes, sizeof(a.bytes)))};
    return trie_db_read_account(
        hashed_account_address,
        std::forward<Cursor>(leaves_cursor),
        std::forward<Cursor>(trie_cursor));
}

MONAD_NAMESPACE_END
