#pragma once

#include <category/execution/ethereum/core/address.hpp>
#include <category/core/basic_formatter.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

template <>
struct quill::copy_loggable<monad::Address> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Address> : public monad::BasicFormatter
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
