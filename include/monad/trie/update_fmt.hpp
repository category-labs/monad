#pragma once

#include <monad/core/basic_formatter.hpp>
#include <monad/trie/nibbles_fmt.hpp>
#include <monad/trie/update.hpp>

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
