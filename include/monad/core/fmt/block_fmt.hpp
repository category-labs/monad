#pragma once

#include <monad/core/basic_formatter.hpp>
#include <monad/core/block.hpp>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/fmt/int_fmt.hpp>
#include <monad/core/fmt/receipt_fmt.hpp>
#include <monad/core/fmt/transaction_fmt.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

template <>
struct quill::copy_loggable<monad::BlockHeader> : std::true_type
{
};

template <>
struct fmt::formatter<monad::BlockHeader> : public monad::BasicFormatter
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
            "Extra Data=0x{:02x} "
            "Base Fee Per Gas={} "
            "Withdrawal Root={}"
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
            fmt::join(std::as_bytes(std::span(bh.extra_data)), ""),
            bh.base_fee_per_gas,
            bh.withdrawals_root);
        return ctx.out();
    }
};
