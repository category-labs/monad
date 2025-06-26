#pragma once

/**
 * @file
 *
 * Defines fmtlib formatters for the C types in `exec_event_ctypes.h`
 */

#include <bit>
#include <cstddef>
#include <iterator>
#include <quill/bundled/fmt/format.h>
#include <span>
#include <string_view>
#include <utility>

#include <category/execution/ethereum/core/fmt/eth_ctypes_fmt.hpp>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

template <>
struct fmt::formatter<monad_exec_flow_type> : fmt::formatter<uint8_t>
{
    template <typename FormatContext>
    auto format(monad_exec_flow_type const &value, FormatContext &ctx) const
    {
        return fmt::formatter<uint8_t>::format(std::to_underlying(value), ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_block_tag> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_exec_block_tag const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "block_tag {{");
        i = fmt::format_to(i, "id = {}", value.id);
        i = fmt::format_to(i, ", block_number = {}", value.block_number);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_block_start> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_exec_block_start const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "block_start {{");
        i = fmt::format_to(i, "block_tag = {}", value.block_tag);
        i = fmt::format_to(i, ", round = {}", value.round);
        i = fmt::format_to(i, ", epoch = {}", value.epoch);
        i = fmt::format_to(i, ", parent_eth_hash = {}", value.parent_eth_hash);
        i = fmt::format_to(i, ", chain_id = {}", value.chain_id);
        i = fmt::format_to(i, ", exec_input = {}", value.exec_input);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_block_end> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_exec_block_end const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "block_end {{");
        i = fmt::format_to(i, "eth_block_hash = {}", value.eth_block_hash);
        i = fmt::format_to(i, ", exec_output = {}", value.exec_output);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_block_qc> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_exec_block_qc const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "block_qc {{");
        i = fmt::format_to(i, "block_tag = {}", value.block_tag);
        i = fmt::format_to(i, ", round = {}", value.round);
        i = fmt::format_to(i, ", epoch = {}", value.epoch);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_block_verified>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_exec_block_verified const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "block_verified {{");
        i = fmt::format_to(i, "block_number = {}", value.block_number);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_txn_start> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_exec_txn_start const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "txn_start {{");
        i = fmt::format_to(
            i, "ingest_epoch_nanos = {}", value.ingest_epoch_nanos);
        i = fmt::format_to(i, ", txn_hash = {}", value.txn_hash);
        i = fmt::format_to(i, ", sender = {}", value.sender);
        i = fmt::format_to(i, ", txn_header = {}", value.txn_header);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_txn_evm_output>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_exec_txn_evm_output const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "txn_evm_output {{");
        i = fmt::format_to(i, "receipt = {}", value.receipt);
        i = fmt::format_to(
            i, ", call_frame_count = {}", value.call_frame_count);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_txn_call_frame>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_exec_txn_call_frame const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "txn_call_frame {{");
        i = fmt::format_to(i, "index = {}", value.index);
        i = fmt::format_to(i, ", caller = {}", value.caller);
        i = fmt::format_to(i, ", call_target = {}", value.call_target);
        i = fmt::format_to(i, ", opcode = {}", value.opcode);
        i = fmt::format_to(i, ", value = {}", value.value);
        i = fmt::format_to(i, ", gas = {}", value.gas);
        i = fmt::format_to(i, ", gas_used = {}", value.gas_used);
        i = fmt::format_to(i, ", evmc_status = {}", value.evmc_status);
        i = fmt::format_to(i, ", depth = {}", value.depth);
        i = fmt::format_to(i, ", input_length = {}", value.input_length);
        i = fmt::format_to(i, ", return_length = {}", value.return_length);
        *i++ = '}';
        auto const *p = std::bit_cast<std::byte const *>(&value + 1);
        i = fmt::format_to(
            i,
            ", input = {}",
            std::span{
                std::bit_cast<uint8_t const *>(p),
                static_cast<size_t>(value.input_length)});
        p += value.input_length * sizeof(uint8_t);
        i = fmt::format_to(
            i,
            ", return = {}",
            std::span{
                std::bit_cast<uint8_t const *>(p),
                static_cast<size_t>(value.return_length)});
        p += value.return_length * sizeof(uint8_t);
        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_account_access_context>
    : fmt::formatter<uint8_t>
{
    template <typename FormatContext>
    auto format(
        monad_exec_account_access_context const &value,
        FormatContext &ctx) const
    {
        return fmt::formatter<uint8_t>::format(std::to_underlying(value), ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_account_access_list_header>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(
        monad_exec_account_access_list_header const &value,
        FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "account_access_list_header {{");
        i = fmt::format_to(i, "entry_count = {}", value.entry_count);
        i = fmt::format_to(i, ", access_context = {}", value.access_context);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_account_access>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_exec_account_access const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "account_access {{");
        i = fmt::format_to(i, "index = {}", value.index);
        i = fmt::format_to(i, ", address = {}", value.address);
        i = fmt::format_to(i, ", access_context = {}", value.access_context);
        i = fmt::format_to(
            i, ", is_balance_modified = {}", value.is_balance_modified);
        i = fmt::format_to(
            i, ", is_nonce_modified = {}", value.is_nonce_modified);
        i = fmt::format_to(i, ", prestate = {}", value.prestate);
        i = fmt::format_to(
            i, ", modified_balance = {}", value.modified_balance);
        i = fmt::format_to(i, ", modified_nonce = {}", value.modified_nonce);
        i = fmt::format_to(
            i, ", storage_key_count = {}", value.storage_key_count);
        i = fmt::format_to(i, ", transient_count = {}", value.transient_count);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_storage_access>
    : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto
    format(monad_exec_storage_access const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "storage_access {{");
        i = fmt::format_to(i, "address = {}", value.address);
        i = fmt::format_to(i, ", index = {}", value.index);
        i = fmt::format_to(i, ", access_context = {}", value.access_context);
        i = fmt::format_to(i, ", modified = {}", value.modified);
        i = fmt::format_to(i, ", transient = {}", value.transient);
        i = fmt::format_to(i, ", key = {}", value.key);
        i = fmt::format_to(i, ", start_value = {}", value.start_value);
        i = fmt::format_to(i, ", end_value = {}", value.end_value);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

template <>
struct fmt::formatter<monad_exec_evm_error> : fmt::formatter<std::string_view>
{
    template <typename FormatContext>
    auto format(monad_exec_evm_error const &value, FormatContext &ctx) const
    {
        fmt::memory_buffer mb;
        std::back_insert_iterator i{mb};
        i = fmt::format_to(i, "evm_error {{");
        i = fmt::format_to(i, "domain_id = {}", value.domain_id);
        i = fmt::format_to(i, ", status_code = {}", value.status_code);
        *i++ = '}';

        std::string_view const view{mb.data(), mb.size()};
        return fmt::formatter<std::string_view>::format(view, ctx);
    }
};

namespace monad
{

    template <std::output_iterator<char> Out>
    Out
    format_as(Out o, void const *payload_buf, monad_exec_event_type event_type)
    {
        switch (event_type) {
        case MONAD_EXEC_BLOCK_START:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_block_start const *>(payload_buf));
        case MONAD_EXEC_BLOCK_REJECT:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_block_reject const *>(payload_buf));
        case MONAD_EXEC_BLOCK_PERF_EVM_ENTER:
            return o;
        case MONAD_EXEC_BLOCK_PERF_EVM_EXIT:
            return o;
        case MONAD_EXEC_BLOCK_END:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_block_end const *>(payload_buf));
        case MONAD_EXEC_BLOCK_QC:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_block_qc const *>(payload_buf));
        case MONAD_EXEC_BLOCK_FINALIZED:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_block_finalized const *>(payload_buf));
        case MONAD_EXEC_BLOCK_VERIFIED:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_block_verified const *>(payload_buf));
        case MONAD_EXEC_TXN_START:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_txn_start const *>(payload_buf));
        case MONAD_EXEC_TXN_REJECT:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_txn_reject const *>(payload_buf));
        case MONAD_EXEC_TXN_PERF_EVM_ENTER:
            return o;
        case MONAD_EXEC_TXN_PERF_EVM_EXIT:
            return o;
        case MONAD_EXEC_TXN_EVM_OUTPUT:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_txn_evm_output const *>(payload_buf));
        case MONAD_EXEC_TXN_LOG:
            return fmt::format_to(
                o, "{}", *static_cast<monad_exec_txn_log const *>(payload_buf));
        case MONAD_EXEC_TXN_CALL_FRAME:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_txn_call_frame const *>(payload_buf));
        case MONAD_EXEC_TXN_END:
            return o;
        case MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_account_access_list_header const *>(
                    payload_buf));
        case MONAD_EXEC_ACCOUNT_ACCESS:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_account_access const *>(payload_buf));
        case MONAD_EXEC_STORAGE_ACCESS:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_storage_access const *>(payload_buf));
        case MONAD_EXEC_EVM_ERROR:
            return fmt::format_to(
                o,
                "{}",
                *static_cast<monad_exec_evm_error const *>(payload_buf));
        default:
            return fmt::format_to(
                o, "unknown exec type code {}", std::to_underlying(event_type));
        }
        std::unreachable();
    }

} // namespace monad
