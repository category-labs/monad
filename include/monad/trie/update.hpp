#pragma once

#include <monad/core/basic_formatter.hpp>
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

template <>
struct quill::copy_loggable<monad::trie::Update> : std::true_type
{
};

template <>
struct fmt::formatter<monad::trie::Upsert> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Upsert const &u, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "UPSERT{{key={} value=0x{:02x}}}",
            u.key,
            fmt::join(std::as_bytes(std::span{u.value}), ""));
        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::trie::Delete> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Delete const &d, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "DELETE{{key={}}}", d.key);
        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::trie::Update> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::trie::Update const &update, FormatContext &ctx) const
    {
        std::visit(
            [&ctx](auto const &u) { fmt::format_to(ctx.out(), "{}", u); },
            update);
        return ctx.out();
    }
};
