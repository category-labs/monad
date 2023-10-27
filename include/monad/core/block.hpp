#pragma once

#include <monad/config.hpp>

#include <monad/core/address.hpp>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>

#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

using block_num_t = uint64_t;

struct BlockHeader
{
    Receipt::Bloom logs_bloom{};
    bytes32_t parent_hash{};
    bytes32_t ommers_hash{};
    bytes32_t state_root{};
    bytes32_t transactions_root{};
    bytes32_t receipts_root{};
    bytes32_t prev_randao{}; // aka mix_hash
    uint256_t difficulty{};

    uint64_t number{0};
    uint64_t gas_limit{0};
    uint64_t gas_used{0};
    uint64_t timestamp{0};

    byte_string_fixed<8> nonce{};
    byte_string extra_data{};

    address_t beneficiary{};

    std::optional<uint256_t> base_fee_per_gas{std::nullopt}; // EIP-1559
    std::optional<bytes32_t> withdrawals_root{std::nullopt}; // EIP-4895

    friend bool operator==(BlockHeader const &, BlockHeader const &) = default;
};

struct Block
{
    BlockHeader header;
    std::vector<Transaction> transactions{};
    std::vector<BlockHeader> ommers{};
    std::optional<std::vector<Withdrawal>> withdrawals{std::nullopt};
};

static_assert(sizeof(BlockHeader) == 656);
static_assert(alignof(BlockHeader) == 8);

static_assert(sizeof(Block) == 736);
static_assert(alignof(Block) == 8);

MONAD_NAMESPACE_END

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
