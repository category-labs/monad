#pragma once

/**
 * @file
 *
 * Defines fmtlib formatters for the C types in `eth_ctypes.h`
 */

#include <bit>
#include <cstddef>
#include <iterator>
#include <quill/bundled/fmt/format.h>
#include <span>
#include <string_view>
#include <utility>

#include <category/execution/ethereum/core/eth_ctypes.h>
#include <category/execution/ethereum/core/fmt/address_fmt.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/fmt/int_fmt.hpp>

template <>
struct fmt::formatter<monad_c_transaction_type> : fmt::formatter<uint8_t>
{
    template <typename FormatContext>
    auto format(monad_c_transaction_type const &value, FormatContext &ctx) const
    {
        return fmt::formatter<uint8_t>::format(std::to_underlying(value), ctx);
    }
};

template <>
struct fmt::formatter<monad_c_access_list_entry>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_c_access_list_entry const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "access_list_entry {{");
        i = fmt::format_to(i, "address = {}", value.address);
        i = fmt::format_to(
            i, ", storage_key_count = {}", value.storage_key_count);
        *i++ = '}';
        auto const *p = std::bit_cast<std::byte const *>(&value + 1);
        i = fmt::format_to(
            i,
            ", storage_key list = {}",
            std::span{
                std::bit_cast<monad_c_bytes32 const *>(p),
                static_cast<size_t>(value.storage_key_count)});
        p += value.storage_key_count * sizeof(monad_c_bytes32);
        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_c_eth_txn_header> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_c_eth_txn_header const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "eth_txn_header {{");
        i = fmt::format_to(i, "txn_type = {}", value.txn_type);
        i = fmt::format_to(i, ", chain_id = {}", value.chain_id);
        i = fmt::format_to(i, ", nonce = {}", value.nonce);
        i = fmt::format_to(i, ", gas_limit = {}", value.gas_limit);
        i = fmt::format_to(i, ", max_fee_per_gas = {}", value.max_fee_per_gas);
        i = fmt::format_to(
            i,
            ", max_priority_fee_per_gas = {}",
            value.max_priority_fee_per_gas);
        i = fmt::format_to(i, ", value = {}", value.value);
        i = fmt::format_to(i, ", to = {}", value.to);
        i = fmt::format_to(
            i, ", is_contract_creation = {}", value.is_contract_creation);
        i = fmt::format_to(i, ", r = {}", value.r);
        i = fmt::format_to(i, ", s = {}", value.s);
        i = fmt::format_to(i, ", y_parity = {}", value.y_parity);
        i = fmt::format_to(i, ", data_length = {}", value.data_length);
        i = fmt::format_to(
            i, ", access_list_count = {}", value.access_list_count);
        *i++ = '}';
        auto const *p = std::bit_cast<std::byte const *>(&value + 1);
        i = fmt::format_to(
            i,
            ", data = {}",
            std::span{
                std::bit_cast<uint8_t const *>(p),
                static_cast<size_t>(value.data_length)});
        p += value.data_length * sizeof(uint8_t);
        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_c_eth_txn_receipt>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_c_eth_txn_receipt const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "eth_txn_receipt {{");
        i = fmt::format_to(i, "status = {}", value.status);
        i = fmt::format_to(i, ", log_count = {}", value.log_count);
        i = fmt::format_to(i, ", gas_used = {}", value.gas_used);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_c_eth_txn_log> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_c_eth_txn_log const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "eth_txn_log {{");
        i = fmt::format_to(i, "index = {}", value.index);
        i = fmt::format_to(i, ", address = {}", value.address);
        i = fmt::format_to(i, ", topic_count = {}", value.topic_count);
        i = fmt::format_to(i, ", data_length = {}", value.data_length);
        *i++ = '}';
        auto const *p = std::bit_cast<std::byte const *>(&value + 1);
        i = fmt::format_to(
            i,
            ", topic list = {}",
            std::span{
                std::bit_cast<monad_c_bytes32 const *>(p),
                static_cast<size_t>(value.topic_count)});
        p += value.topic_count * sizeof(monad_c_bytes32);
        i = fmt::format_to(
            i,
            ", data = {}",
            std::span{
                std::bit_cast<uint8_t const *>(p),
                static_cast<size_t>(value.data_length)});
        p += value.data_length * sizeof(uint8_t);
        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_c_eth_account_state>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_c_eth_account_state const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "eth_account_state {{");
        i = fmt::format_to(i, "nonce = {}", value.nonce);
        i = fmt::format_to(i, ", balance = {}", value.balance);
        i = fmt::format_to(i, ", code_hash = {}", value.code_hash);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_c_eth_block_exec_input>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_c_eth_block_exec_input const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "eth_block_exec_input {{");
        i = fmt::format_to(i, "ommers_hash = {}", value.ommers_hash);
        i = fmt::format_to(i, ", beneficiary = {}", value.beneficiary);
        i = fmt::format_to(
            i, ", transactions_root = {}", value.transactions_root);
        i = fmt::format_to(i, ", difficulty = {}", value.difficulty);
        i = fmt::format_to(i, ", number = {}", value.number);
        i = fmt::format_to(i, ", gas_limit = {}", value.gas_limit);
        i = fmt::format_to(i, ", timestamp = {}", value.timestamp);
        i = fmt::format_to(i, ", extra_data = {}", value.extra_data);
        i = fmt::format_to(
            i, ", extra_data_length = {}", value.extra_data_length);
        i = fmt::format_to(i, ", prev_randao = {}", value.prev_randao);
        i = fmt::format_to(i, ", nonce = {}", value.nonce);
        i = fmt::format_to(
            i, ", base_fee_per_gas = {}", value.base_fee_per_gas);
        i = fmt::format_to(
            i, ", withdrawals_root = {}", value.withdrawals_root);
        i = fmt::format_to(i, ", txn_count = {}", value.txn_count);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_c_eth_block_exec_output>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_c_eth_block_exec_output const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "eth_block_exec_output {{");
        i = fmt::format_to(i, "state_root = {}", value.state_root);
        i = fmt::format_to(i, ", receipts_root = {}", value.receipts_root);
        i = fmt::format_to(i, ", logs_bloom = {}", value.logs_bloom);
        i = fmt::format_to(i, ", gas_used = {}", value.gas_used);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};
