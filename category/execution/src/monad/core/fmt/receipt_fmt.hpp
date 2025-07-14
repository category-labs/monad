#pragma once

#include <category/core/basic_formatter.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/fmt/transaction_fmt.hpp>
#include <monad/core/receipt.hpp>

template <>
struct quill::copy_loggable<monad::Receipt::Log> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::Receipt> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Receipt::Log> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Receipt::Log const &l, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Log{{"
            "Data=0x{:02x} "
            "Topics={} "
            "Address={}"
            "}}",
            fmt::join(std::as_bytes(std::span(l.data)), ""),
            l.topics,
            l.address);
        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::Receipt> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Receipt const &r, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Receipt{{"
            "Bloom=0x{:02x} "
            "Status={} "
            "Gas Used={} "
            "Transaction Type={} "
            "Logs={}"
            "}}",
            fmt::join(std::as_bytes(std::span(r.bloom)), ""),
            r.status,
            r.gas_used,
            r.type,
            r.logs);
        return ctx.out();
    }
};
