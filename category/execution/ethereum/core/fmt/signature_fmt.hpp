#pragma once

#include <category/core/basic_formatter.hpp>
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>
#include <category/execution/ethereum/core/signature.hpp>

#include <quill/Quill.h>

template <>
struct quill::copy_loggable<monad::SignatureAndChain> : std::true_type
{
};

template <>
struct fmt::formatter<monad::SignatureAndChain> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::SignatureAndChain const &sc, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "SignatureAndChain{{"
            "r={} "
            "s={} "
            "chain_id={} "
            "y_parity={}"
            "}}",
            sc.r,
            sc.s,
            sc.chain_id,
            sc.y_parity);
        return ctx.out();
    }
};
