#pragma once

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/logging/config.hpp>

#include <monad/trie/nibbles.hpp>
#include <monad/trie/update.hpp>

#include <quill/Quill.h>

#include <optional>
#include <type_traits>

#include <iostream>

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

template <size_t N>
struct fmt_byte_string_fixed_wrapper
{
    byte_string_fixed<N> bsf;
    explicit fmt_byte_string_fixed_wrapper(byte_string_fixed<N> const &arg)
        : bsf(arg)
    {
    }
};

MONAD_LOG_NAMESPACE_END

namespace quill
{
    template <>
    struct copy_loggable<monad::address_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::BlockHeader> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::bytes32_t> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::log::fmt_byte_string_wrapper> : std::true_type
    {
    };

    template <size_t N>
    struct copy_loggable<monad::log::fmt_byte_string_fixed_wrapper<N>>
        : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::Receipt> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::Receipt::Log> : std::true_type
    {
    };

    template <>
    struct copy_loggable<monad::Transaction::Type> : std::true_type
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

    template <unsigned N>
    struct copy_loggable<intx::uint<N>> : std::true_type
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
    struct formatter<monad::BlockHeader> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::BlockHeader const &bh, FormatContext &ctx) const
        {
            fmt::format_to(
                ctx.out(),
                "BlockHeader{{"
                "Parent Hash={} "
                "Ommers Hash={} "
                "Beneficiary Address={} "
                "State Root={} "
                "Transaction Root={} "
                "Receipt Root={} "
                "Logs Bloom={} "
                "Difficulty={} "
                "Block Number={} "
                "Gas Limit={} "
                "Gas Used={} "
                "Timestamp={} "
                "Extra Data={}"
                "}}",
                bh.parent_hash,
                bh.ommers_hash,
                bh.beneficiary,
                bh.state_root,
                bh.transactions_root,
                bh.receipts_root,
                monad::log::fmt_byte_string_fixed_wrapper(bh.logs_bloom),
                bh.difficulty,
                bh.number,
                bh.gas_limit,
                bh.gas_used,
                bh.timestamp,
                monad::log::fmt_byte_string_wrapper{.bs = bh.extra_data});
            return ctx.out();
        }
    };

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

    template <size_t N>
    struct formatter<monad::log::fmt_byte_string_fixed_wrapper<N>>
        : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(
            monad::log::fmt_byte_string_fixed_wrapper<N> const &value,
            FormatContext &ctx) const
        {
            fmt::format_to(ctx.out(), "0x");
            for (auto const &v : value.bsf) {
                fmt::format_to(ctx.out(), "{:02x}", v);
            }
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::Receipt> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::Receipt const &r, FormatContext &ctx) const
        {
            fmt::format_to(
                ctx.out(),
                "Receipt{{"
                "Bloom={} "
                "Status={} "
                "Gas Used={} "
                "Transaction Type={} "
                "Logs={}"
                "}}",
                monad::log::fmt_byte_string_fixed_wrapper(r.bloom),
                r.status,
                r.gas_used,
                r.type,
                r.logs);
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::Receipt::Log> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::Receipt::Log const &l, FormatContext &ctx) const
        {
            fmt::format_to(
                ctx.out(),
                "Log{{"
                "Data={} "
                "Topics={} "
                "Address={}"
                "}}",
                monad::log::fmt_byte_string_wrapper{.bs = l.data},
                l.topics,
                l.address);
            return ctx.out();
        }
    };

    template <>
    struct formatter<monad::Transaction::Type>
        : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(monad::Transaction::Type const &t, FormatContext &ctx) const
        {
            if (t == monad::Transaction::Type::eip155) {
                fmt::format_to(ctx.out(), "eip155");
            }
            else if (t == monad::Transaction::Type::eip2930) {
                fmt::format_to(ctx.out(), "eip2930");
            }
            else if (t == monad::Transaction::Type::eip1559) {
                fmt::format_to(ctx.out(), "eip1559");
            }
            else {
                fmt::format_to(ctx.out(), "Unknown Transaction Type");
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

    template <unsigned N>
    struct formatter<intx::uint<N>> : public monad::log::basic_formatter
    {
        template <typename FormatContext>
        auto format(intx::uint<N> const &value, FormatContext &ctx) const
        {
            fmt::format_to(ctx.out(), "{}", intx::to_string(value));
            return ctx.out();
        }
    };
}
