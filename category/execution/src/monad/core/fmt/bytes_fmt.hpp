#pragma once

#include <category/core/basic_formatter.hpp>
#include <category/core/bytes.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

template <>
struct quill::copy_loggable<monad::bytes32_t> : std::true_type
{
};

template <>
struct fmt::formatter<monad::bytes32_t> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::bytes32_t const &value, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "0x{:02x}",
            fmt::join(std::as_bytes(std::span(value.bytes)), ""));
        return ctx.out();
    }
};
