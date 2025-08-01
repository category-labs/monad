#pragma once

#include <category/core/basic_formatter.hpp>
#include <category/core/block.hpp>
#include <category/core/fmt/address_fmt.hpp>
#include <category/core/fmt/bytes_fmt.hpp>
#include <category/core/fmt/int_fmt.hpp>
#include <category/core/fmt/receipt_fmt.hpp>
#include <category/core/fmt/transaction_fmt.hpp>

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
            "Mixhash={} "
            "Logs Bloom=0x{:02x} "
            "Difficulty={} "
            "Block Number={} "
            "Gas Limit={} "
            "Gas Used={} "
            "Timestamp={} "
            "Nonce={} "
            "Extra Data=0x{:02x} "
            "Base Fee Per Gas={} "
            "Withdrawal Root={} "
            "Blob Gas Used={} "
            "Excess Blob Gas={} "
            "Parent Beacon Block Root={}"
            "}}",
            bh.parent_hash,
            bh.ommers_hash,
            bh.beneficiary,
            bh.state_root,
            bh.transactions_root,
            bh.receipts_root,
            bh.prev_randao,
            fmt::join(std::as_bytes(std::span(bh.logs_bloom)), ""),
            bh.difficulty,
            bh.number,
            bh.gas_limit,
            bh.gas_used,
            bh.timestamp,
            fmt::join(std::as_bytes(std::span(bh.nonce)), ""),
            fmt::join(std::as_bytes(std::span(bh.extra_data)), ""),
            bh.base_fee_per_gas,
            bh.withdrawals_root,
            bh.blob_gas_used,
            bh.excess_blob_gas,
            bh.parent_beacon_block_root);
        return ctx.out();
    }
};
