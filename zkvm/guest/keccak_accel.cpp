// Copyright (C) 2025-26 Category Labs, Inc.
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

// ZisK Keccak-256: absorb 136-byte blocks as 17 words, then call the
// Keccak-f precompile. Apply Ethereum's 0x01/0x80 padding to the final block.

#ifdef MONAD_ZKVM_ZISK

    #include <cstddef>
    #include <cstdint>
    #include <cstring>

constexpr size_t KECCAK_RATE = 136;
constexpr size_t KECCAK_CAPACITY_BYTES = 64;

// Load eight bytes without requiring pointer alignment.
[[gnu::always_inline]] static inline uint64_t
load64(unsigned char const *const bytes)
{
    uint64_t word;
    __builtin_memcpy(&word, bytes, sizeof word);
    return word;
}

extern "C"
{

// Inline ZisK's Keccak-f marker (CSR 0x800) to avoid call/return overhead.
// The precompile updates state in place; the memory clobber tells the
// compiler that this instruction reads and writes memory.
[[gnu::always_inline]] inline void zisk_keccakf(uint64_t (*state)[25]) noexcept
{
    asm volatile(".option push\n\t"
                 ".option arch, +zicsr\n\t"
                 "csrs 0x800, %0\n\t"
                 ".option pop"
                 :
                 : "r"(state)
                 : "memory");
}

static inline void keccak_permute(uint64_t (*state)[25])
{
    zisk_keccakf(state);
}

void monad_zkvm_keccak256_fast(
    void const *const input, size_t remaining_bytes, uint8_t output[32])
{
    constexpr size_t RATE_WORDS = KECCAK_RATE / 8; // 17

    // Keccak-f[1600] uses 25 lanes of 64 bits (200 bytes).
    // Keccak-256 absorbs into the first 17 lanes (136-byte rate);
    // the remaining 8 lanes form the capacity.
    uint64_t state[25];
    // Skip 17 words (136 bytes) and zero only the 64-byte capacity.
    std::memset(state + RATE_WORDS, 0, KECCAK_CAPACITY_BYTES);
    if (remaining_bytes < KECCAK_RATE) {
        // Zero the rate before copying short inputs and adding padding.
        // On ZisK 1.4, this aligned, fixed-size clear measured cheaper than
        // clearing only the variable-length, potentially unaligned tail.
        std::memset(state, 0, KECCAK_RATE);
    }
    auto const *input_cursor = static_cast<unsigned char const *>(input);

    // Copy the first block into the uninitialized rate; XOR later blocks.
    // With -mzisk-dma, the copy uses ZisK's block-move precompile.
    bool is_first_block = true;
    while (remaining_bytes >= KECCAK_RATE) {
        if (is_first_block) {
            // Initialize all 136 rate bytes before the first permutation.
            std::memcpy(state, input_cursor, KECCAK_RATE);
            is_first_block = false;
        }
        else {
            for (size_t i = 0; i < RATE_WORDS; ++i) {
                state[i] ^= load64(input_cursor + 8 * i);
            }
        }
        keccak_permute(&state);
        input_cursor += KECCAK_RATE;
        remaining_bytes -= KECCAK_RATE;
    }

    // Final block: remainder plus pad10*1 with the 0x01 domain byte.
    if (is_first_block) {
        // No full block was absorbed; pad directly in the zeroed state.
        if (remaining_bytes) {
            std::memcpy(state, input_cursor, remaining_bytes);
        }
        auto *const state_bytes = reinterpret_cast<unsigned char *>(state);
        state_bytes[remaining_bytes] = 0x01;
        // Set the final padding bit through aligned lane 16 (byte 135).
        static_assert(KECCAK_RATE - 1 == 16 * 8 + 7);
        state[16] |= uint64_t{0x80} << 56;
    }
    else {
        alignas(8) unsigned char final_block[KECCAK_RATE] = {};
        if (remaining_bytes) {
            std::memcpy(final_block, input_cursor, remaining_bytes);
        }
        final_block[remaining_bytes] = 0x01;
        // Skip trailing zero lanes; fixed counts preserve loop unrolling.
        // A runtime count measured worse.
        if (remaining_bytes <= 31) {
            for (size_t i = 0; i < 4; ++i) {
                state[i] ^= load64(final_block + 8 * i);
            }
        }
        else if (remaining_bytes <= 63) {
            for (size_t i = 0; i < 8; ++i) {
                state[i] ^= load64(final_block + 8 * i);
            }
        }
        else if (remaining_bytes <= 95) {
            for (size_t i = 0; i < 12; ++i) {
                state[i] ^= load64(final_block + 8 * i);
            }
        }
        else if (remaining_bytes <= 127) {
            for (size_t i = 0; i < 16; ++i) {
                state[i] ^= load64(final_block + 8 * i);
            }
        }
        else {
            for (size_t i = 0; i < RATE_WORDS; ++i) {
                state[i] ^= load64(final_block + 8 * i);
            }
        }
        // Fold the final padding bit directly into the state, avoiding
        // a byte read-modify-write in final_block.
        state[16] ^= uint64_t{0x80} << 56;
    }
    keccak_permute(&state);

    std::memcpy(output, state, 32);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK
