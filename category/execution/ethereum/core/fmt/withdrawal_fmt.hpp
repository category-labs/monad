#pragma once

#include <category/core/basic_formatter.hpp>
#include <category/core/withdrawal.hpp>

template <>
struct quill::copy_loggable<monad::Withdrawal> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Withdrawal> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Withdrawal const &w, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Withdrawal{{"
            "Index={} "
            "Validator Index={} "
            "Amount={} "
            "Recipient={}"
            "}}",
            w.index,
            w.validator_index,
            w.amount,
            w.recipient);
        return ctx.out();
    }
};
