#pragma once

#include <category/core/basic_formatter.hpp>
#include <category/core/int.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

template <unsigned N>
struct quill::copy_loggable<intx::uint<N>> : std::true_type
{
};

template <unsigned N>
struct fmt::formatter<intx::uint<N>> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(intx::uint<N> const &value, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "{}", intx::to_string(value, 10));
        return ctx.out();
    }
};
