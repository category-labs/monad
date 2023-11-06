#pragma once

#include <monad/core/basic_formatter.hpp>
#include <monad/core/transaction.hpp>

template <>
struct quill::copy_loggable<monad::TransactionType> : std::true_type
{
};

template <>
struct fmt::formatter<monad::TransactionType> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::TransactionType const &t, FormatContext &ctx) const
    {
        if (t == monad::TransactionType::eip155) {
            fmt::format_to(ctx.out(), "eip155");
        }
        else if (t == monad::TransactionType::eip2930) {
            fmt::format_to(ctx.out(), "eip2930");
        }
        else if (t == monad::TransactionType::eip1559) {
            fmt::format_to(ctx.out(), "eip1559");
        }
        else {
            fmt::format_to(ctx.out(), "Unknown Transaction Type");
        }
        return ctx.out();
    }
};
