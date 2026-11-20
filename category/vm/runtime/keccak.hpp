// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/bytes_match.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/bin.hpp>
#include <category/vm/runtime/types.hpp>

#include <cstring>

namespace monad::vm::runtime
{
#if defined(MONAD_ZKVM_ZISK)
    // Mapping-slot lookups often hash the same 64 bytes. Cache the EVM stack
    // word so a hit skips both Keccak and the conversion from big endian.
    struct alignas(128) Sha3CacheEntry
    {
        uint8_t input[64];
        uint256_t result;
        uint64_t valid;
    };

    static_assert(sizeof(Sha3CacheEntry) == 128);
    inline constinit Sha3CacheEntry sha3_cache[2048]{};

    [[gnu::always_inline]] inline Sha3CacheEntry &
    sha3_cache_entry(uint8_t const *input) noexcept
    {
        // Mix the last word of each 32-byte operand to select a candidate.
        uint64_t key_tail, slot_tail;
        std::memcpy(&key_tail, input + 24, sizeof(key_tail));
        std::memcpy(&slot_tail, input + 56, sizeof(slot_tail));
        uint64_t const index_bits = key_tail ^ slot_tail;
        return sha3_cache[(index_bits ^ __builtin_bswap64(index_bits)) & 2047u];
    }

    // Return only an exact match; empty slots and index collisions are misses.
    [[gnu::always_inline]] inline uint256_t const *
    find_cached_sha3(uint8_t const *input) noexcept
    {
        auto const &entry = sha3_cache_entry(input);
        return entry.valid && bytes_match<64>(input, entry.input)
                   ? &entry.result
                   : nullptr;
    }

    [[gnu::always_inline]] inline uint256_t
    hash_and_cache_64(uint8_t const *input) noexcept
    {
        auto const result = load_be<uint256_t>(keccak256({input, 64}));
        auto &entry = sha3_cache_entry(input);
        std::memcpy(entry.input, input, sizeof(entry.input));
        entry.result = result;
        entry.valid = 1;
        return result;
    }

    [[gnu::always_inline]] inline uint256_t
    cached_hash_or_compute(uint8_t const *input) noexcept
    {
        if (auto const *result = find_cached_sha3(input)) {
            return *result;
        }
        return hash_and_cache_64(input);
    }
#endif
    template <Traits traits>
    // Keep the memory expansion and hash outside the fixed-size opcode slot.
    MONAD_VM_RUNTIME_NOINLINE inline void sha3(
        Context *ctx, uint256_t *result_ptr, uint256_t const *offset_ptr,
        uint256_t const *size_ptr)
    {
        Memory::Offset offset;
        auto const size = ctx->get_memory_offset(*size_ptr);

        if (*size > 0) {
            offset = ctx->get_memory_offset(*offset_ptr);

            ctx->expand_memory<traits>(offset + size);

            auto const word_size = shr_ceil<5>(size);
            ctx->deduct_gas(word_size * bin<6>);
        }

#if defined(MONAD_ZKVM_ZISK)
        if (*size == 64) {
            // Memory expansion and gas charging must precede cache reuse.
            *result_ptr = cached_hash_or_compute(ctx->memory.data + *offset);
            return;
        }
#endif
        auto const hash = keccak256({ctx->memory.data + *offset, *size});
        *result_ptr = load_be<uint256_t>(hash);
    }
}
