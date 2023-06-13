#pragma once

#include <monad/execution/replay_block_db.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/update.hpp>

#include <quill/Quill.h>

#include <type_traits>

MONAD_LOG_NAMESPACE_BEGIN
struct basic_formatter
{
    template <typename ParseContext>
    constexpr auto parse(ParseContext &ctx)
    {
        return ctx.begin();
    }
};

// https://github.com/fmtlib/fmt/issues/1621
struct fmt_byte_string_wrapper
{
    byte_string bs;
};
MONAD_LOG_NAMESPACE_END

namespace quill
{
    template <>
    struct copy_loggable<monad::bytes32_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::address_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::trie::Nibbles> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::trie::Update> : std::true_type
    {
    };

    template <>
    struct copy_loggable<uint64_t> : std::true_type
    {
    };

    template <typename T>
    struct copy_loggable<std::optional<T>>
        : std::integral_constant<bool, detail::is_registered_copyable_v<T>>
    {
    };
}

namespace fmt
{
    template <>
    struct formatter<monad::bytes32_t> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::bytes32_t const &value, FormatContext &ctx) const
        {
            fmt::format_to(ctx.out(), "0x");
            for (auto const &v : value.bytes) {
                fmt::format_to(ctx.out(), "{:02x}", v);
            }
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::address_t> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::address_t const &value, FormatContext &ctx) const
        {
            fmt::format_to(ctx.out(), "0x");
            for (auto const &v : value.bytes) {
                fmt::format_to(ctx.out(), "{:02x}", v);
            }
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::trie::Nibbles> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::trie::Nibbles const &n, FormatContext &ctx) const
        {
            fmt::format_to(ctx.out(), "Nibbles{{0x");
            for (uint8_t i = 0; i < n.size(); ++i) {
                MONAD_DEBUG_ASSERT(n[i] <= 0xf);
                fmt::format_to(ctx.out(), "{:01x}", n[i]);
            }
            fmt::format_to(ctx.out(), "}}");
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::log::fmt_byte_string_wrapper>
        : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(
            monad::log::fmt_byte_string_wrapper const &b,
            FormatContext &ctx) const
        {
            fmt::format_to(ctx.out(), "0x");
            for (auto const &v : b.bs) {
                fmt::format_to(ctx.out(), "{:02x}", v);
            }
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::trie::Upsert> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::trie::Upsert const &u, FormatContext &ctx) const
        {
            fmt::format_to(
                ctx.out(),
                "Upsert{{{} {}}}",
                u.key,
                monad::log::fmt_byte_string_wrapper{.bs = u.value});
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::trie::Delete> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::trie::Delete const &d, FormatContext &ctx) const
        {
            fmt::format_to(ctx.out(), "Delete{{{}}}", d.key);
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::trie::Update> : public monad::log::basic_formatter
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
}
