#pragma once

#include <monad/vm/runtime/transmute.hpp>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

namespace monad::vm::runtime
{
    inline void log_impl(
        Context *ctx, uint256_t const &offset_word, uint256_t const &size_word,
        std::span<evmc::bytes32 const> topics)
    {
        if (MONAD_VM_UNLIKELY(ctx->env.evmc_flags & EVMC_STATIC)) {
            ctx->exit(StatusCode::Error);
        }

        Memory::Offset offset;
        auto size = ctx->get_memory_offset(size_word);

        if (*size > 0) {
            offset = ctx->get_memory_offset(offset_word);
            ctx->expand_memory(offset + size);
            ctx->deduct_gas(size * bin<8>);
        }

        ctx->host->emit_log(
            ctx->context,
            &ctx->env.recipient,
            ctx->memory.data + *offset,
            *size,
            topics.data(),
            topics.size());
    }

    inline void
    log0(Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr)
    {
        log_impl(ctx, *offset_ptr, *size_ptr, {});
    }

    inline void log1(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr)
    {
        log_impl(
            ctx,
            *offset_ptr,
            *size_ptr,
            {{
                bytes32_from_uint256(*topic1_ptr),
            }});
    }

    inline void log2(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr, uint256_t const *topic2_ptr)
    {
        log_impl(
            ctx,
            *offset_ptr,
            *size_ptr,
            {{
                bytes32_from_uint256(*topic1_ptr),
                bytes32_from_uint256(*topic2_ptr),
            }});
    }

    inline void log3(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr, uint256_t const *topic2_ptr,
        uint256_t const *topic3_ptr)
    {
        log_impl(
            ctx,
            *offset_ptr,
            *size_ptr,
            {{
                bytes32_from_uint256(*topic1_ptr),
                bytes32_from_uint256(*topic2_ptr),
                bytes32_from_uint256(*topic3_ptr),
            }});
    }

    inline void log4(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *size_ptr,
        uint256_t const *topic1_ptr, uint256_t const *topic2_ptr,
        uint256_t const *topic3_ptr, uint256_t const *topic4_ptr)
    {
        log_impl(
            ctx,
            *offset_ptr,
            *size_ptr,
            {{
                bytes32_from_uint256(*topic1_ptr),
                bytes32_from_uint256(*topic2_ptr),
                bytes32_from_uint256(*topic3_ptr),
                bytes32_from_uint256(*topic4_ptr),
            }});
    }
}
