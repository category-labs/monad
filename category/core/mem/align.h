#pragma once

/**
 * @file
 *
 * Utilities for manually aligning sizes and addresses
 */

// TODO(ken): <stdbit.h> is not in C++ until C++26 (P3370), for now we have
//  to work around this until we're ready to support -std=c++26 when this
//  C header is included by C++ translation units
#ifdef __cplusplus
    #include <bit>
#else
    #include <stdbit.h>
#endif

#include <stddef.h>

#include <category/core/assert.h>
#include <category/core/bit_util.h>
#include <category/core/likely.h>

#ifdef __cplusplus
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t const size, size_t const align)
{
    MONAD_DEBUG_ASSERT(std::has_single_bit(align));
    return bit_round_up(size, static_cast<unsigned>(std::countr_zero(align)));
}
#else
[[gnu::always_inline]] static inline size_t
monad_round_size_to_align(size_t const size, size_t const align)
{
    // Round size up to the nearest multiple of align. bit_round_up does this,
    // provided that align has the form 2^b and is expressed as `b`. `b` (which
    // is `log_2 align`) is computed efficiently using stdc_trailing_zeros,
    // an intrinsic operation on many platforms (e.g., TZCNT).
    MONAD_DEBUG_ASSERT(stdc_has_single_bit(align));
    return bit_round_up(size, stdc_trailing_zeros(align));
}
#endif
