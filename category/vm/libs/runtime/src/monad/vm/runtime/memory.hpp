#pragma once

#include <monad/vm/runtime/types.hpp>

namespace monad::vm::runtime
{
    inline void
    mload(Context *ctx, uint256_t *result_ptr, uint256_t const *offset_ptr)
    {
        auto offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory(offset + bin<32>);
        *result_ptr = uint256_t::load_be_unsafe(ctx->memory.data + *offset);
    }

    inline void mstore(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory(offset + bin<32>);
        value_ptr->store_be(ctx->memory.data + *offset);
    }

    inline void mstore8(
        Context *ctx, uint256_t const *offset_ptr, uint256_t const *value_ptr)
    {
        auto offset = ctx->get_memory_offset(*offset_ptr);
        ctx->expand_memory(offset + bin<1>);
        ctx->memory.data[*offset] = value_ptr->as_bytes()[0];
    }

    inline void mcopy(
        Context *ctx, uint256_t const *dst_ptr, uint256_t const *src_ptr,
        uint256_t const *size_ptr)
    {
        auto size = ctx->get_memory_offset(*size_ptr);
        if (*size > 0) {
            auto src = ctx->get_memory_offset(*src_ptr);
            auto dst = ctx->get_memory_offset(*dst_ptr);
            ctx->expand_memory(max(dst, src) + size);
            auto size_in_words = shr_ceil<5>(size);
            ctx->deduct_gas(size_in_words * bin<3>);
            std::memmove(
                ctx->memory.data + *dst, ctx->memory.data + *src, *size);
        }
    }
}
