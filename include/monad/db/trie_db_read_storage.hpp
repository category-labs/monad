#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/rlp/decode.hpp>

MONAD_NAMESPACE_BEGIN

template <typename Cursor>
[[nodiscard]] bytes32_t trie_db_read_storage_with_hashed_key(
    address_t const &a, trie::Nibbles const &k, Cursor &&leaves_cursor,
    Cursor &&trie_cursor)
{
    leaves_cursor.set_prefix(a);

    if (MONAD_UNLIKELY(leaves_cursor.empty())) {
        return bytes32_t{};
    }

    auto const [key, exists] = get_trie_key_of_leaf(k, leaves_cursor);

    if (!exists) {
        return bytes32_t{};
    }

    trie_cursor.set_prefix(a);
    trie_cursor.lower_bound(key);

    MONAD_ASSERT(trie_cursor.key().transform([](auto const &key) {
        return key.path();
    }) == key);

    auto const value = trie_cursor.value();
    MONAD_ASSERT(value.has_value());

    auto const node = trie::deserialize_node(key, *value);
    MONAD_ASSERT(std::holds_alternative<trie::Leaf>(node));

    byte_string zeroless;
    auto const rest =
        rlp::decode_string(zeroless, std::get<trie::Leaf>(node).value);
    MONAD_ASSERT(rest.empty());
    MONAD_ASSERT(zeroless.size() <= sizeof(bytes32_t));

    bytes32_t ret;
    std::copy_n(
        zeroless.data(),
        zeroless.size(),
        std::next(
            std::begin(ret.bytes),
            static_cast<uint8_t>(sizeof(bytes32_t) - zeroless.size())));
    MONAD_ASSERT(ret != bytes32_t{});
    return ret;
}

template <typename Cursor>
[[nodiscard]] bytes32_t trie_db_read_storage(
    address_t const &a, bytes32_t const &k, Cursor &&leaves_cursor,
    Cursor &&trie_cursor)
{
    auto const hashed_storage_key = trie::Nibbles{
        std::bit_cast<bytes32_t>(ethash::keccak256(k.bytes, sizeof(k.bytes)))};
    return trie_db_read_storage_with_hashed_key(
        a,
        hashed_storage_key,
        std::forward<Cursor>(leaves_cursor),
        std::forward<Cursor>(trie_cursor));
}

MONAD_NAMESPACE_END
