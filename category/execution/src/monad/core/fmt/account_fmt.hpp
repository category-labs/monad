#pragma once

#include <category/core/basic_formatter.hpp>
#include <monad/core/account.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/fmt/int_fmt.hpp>
#include <monad/types/fmt/incarnation_fmt.hpp>

template <>
struct quill::copy_loggable<monad::Account> : std::true_type
{
};

template <>
struct fmt::formatter<monad::Account> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Account const &a, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "Account{{"
            "balance={}, "
            "code_hash={}, "
            "nonce={}, "
            "incarnation={}"
            "}}",
            a.balance,
            a.code_hash,
            a.nonce,
            a.incarnation);
        return ctx.out();
    }
};
