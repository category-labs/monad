#pragma once

#include <monad/core/address_fmt.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/core/int_fmt.hpp>
#include <monad/core/receipt_fmt.hpp>
#include <monad/core/transaction_fmt.hpp>

template <>
struct quill::copy_loggable<monad::BlockHeader> : std::true_type
{
};

template <>
struct fmt::formatter<monad::BlockHeader> : public monad::basic_formatter
{
    template <typename FormatContext>
    auto format(monad::BlockHeader const &bh, FormatContext &ctx) const
    {
        fmt::format_to(
            ctx.out(),
            "BlockHeader{{"
            "Parent Hash={} "
            "Ommers Hash={} "
            "Beneficiary Address={} "
            "State Root={} "
            "Transaction Root={} "
            "Receipt Root={} "
            "Logs Bloom=0x{:02x} "
            "Difficulty={} "
            "Block Number={} "
            "Gas Limit={} "
            "Gas Used={} "
            "Timestamp={} "
            "Extra Data=0x{:02x}"
            "}}",
            bh.parent_hash,
            bh.ommers_hash,
            bh.beneficiary,
            bh.state_root,
            bh.transactions_root,
            bh.receipts_root,
            fmt::join(std::as_bytes(std::span(bh.logs_bloom)), ""),
            bh.difficulty,
            bh.number,
            bh.gas_limit,
            bh.gas_used,
            bh.timestamp,
            fmt::join(std::as_bytes(std::span(bh.extra_data)), ""));
        return ctx.out();
    }
};
