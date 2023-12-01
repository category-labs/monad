#pragma once

#include <monad/core/address.hpp>
#include <monad/core/basic_formatter.hpp>

template <>
struct quill::copy_loggable<monad::Address> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Address> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::Address const &value, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        return ctx.out();
    }
};
