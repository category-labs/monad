#pragma once

#include <category/core/basic_formatter.hpp>
#include <monad/types/incarnation.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

#include <type_traits>

template <>
struct quill::copy_loggable<monad::Incarnation> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Incarnation> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Incarnation const &incarnation, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Incarnation{{"
            "block={}, "
            "tx={}"
            "}}",
            incarnation.get_block(),
            incarnation.get_tx());
        return ctx.out();
    }
};
