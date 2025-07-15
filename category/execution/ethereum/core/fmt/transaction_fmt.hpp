#pragma once

#include <category/core/basic_formatter.hpp>
#include <category/execution/ethereum/core/fmt/signature_fmt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>

template <>
struct quill::copy_loggable<monad::TransactionType> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::AccessEntry> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::AccessList> : std::true_type
{
};

template <>
struct quill::copy_loggable<monad::Transaction> : std::true_type
{
};

template <>
struct fmt::formatter<monad::TransactionType> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::TransactionType const &t, FormatContext &ctx) const
    {
        if (t == monad::TransactionType::legacy) {
            fmt::format_to(ctx.out(), "legacy");
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

template <>
struct fmt::formatter<monad::AccessEntry> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::AccessEntry const &ae, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "AccessEntry{{"
            "Address={} "
            "Keys={}"
            "}}",
            ae.a,
            ae.keys);

        return ctx.out();
    }
};

template <>
struct fmt::formatter<monad::Transaction> : public monad::BasicFormatter
{
    template <typename FormatContext>
    auto format(monad::Transaction const &tx, FormatContext &ctx) const
    {
        auto const &sender = monad::recover_sender(tx);
        fmt::format_to(
            ctx.out(),
            "Transaction{{"
            "sender={} "
            "sc={} "
            "nonce={} "
            "max_priority_fee_per_gas={} "
            "max_fee_per_gas={} "
            "gas_limit={} "
            "value={} "
            "to={} "
            "type={} "
            "data=0x{:02x} "
            "access_list={}"
            "}} ",
            sender,
            tx.sc,
            tx.nonce,
            tx.max_priority_fee_per_gas,
            tx.max_fee_per_gas,
            tx.gas_limit,
            tx.value,
            tx.to,
            tx.type,
            fmt::join(std::as_bytes(std::span(tx.data)), ""),
            tx.access_list);

        return ctx.out();
    }
};
