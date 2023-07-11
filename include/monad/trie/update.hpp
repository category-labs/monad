#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/trie/config.hpp>
#include <monad/trie/nibbles.hpp>

#include <variant>

MONAD_TRIE_NAMESPACE_BEGIN

struct Upsert
{
    Nibbles key;
    byte_string value;
};

struct Delete
{
    Nibbles key;
};

using Update = std::variant<Upsert, Delete>;

[[nodiscard]] constexpr Nibbles const &get_update_key(Update const &u)
{
    return std::visit(
        [](auto const &ud) -> Nibbles const & { return ud.key; }, u);
}

[[nodiscard]] constexpr bool is_deletion(Update const &u)
{
    return std::holds_alternative<Delete>(u);
}

[[nodiscard]] constexpr byte_string const &get_upsert_value(Update const &u)
{
    return std::get<Upsert>(u).value;
}

MONAD_TRIE_NAMESPACE_END
