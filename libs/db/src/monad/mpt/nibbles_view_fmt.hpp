#pragma once

#include <monad/core/basic_formatter.hpp>
#include <monad/mpt/nibbles_view.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

template <>
struct quill::copy_loggable<monad::mpt::NibblesView> : std::false_type
{
};

template <>
struct fmt::formatter<monad::mpt::NibblesView> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::mpt::NibblesView const &value, FormatContext &ctx) const
    {
        fmt::format_to(ctx.out(), "0x");
        for (auto i = 0u; i < value.nibble_size(); ++i) {
            fmt::format_to(ctx.out(), "{:01x}", value.get(i));
        }
        return ctx.out();
    }
};
