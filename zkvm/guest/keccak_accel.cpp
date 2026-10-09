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

#if defined(MONAD_ZKVM_ZISK) || defined(MONAD_ZKVM_KECCAK_TEST)

#include <cstddef>
#include <cstdint>
#include <cstring>

constexpr size_t KECCAK_RATE = 136;

// Load eight bytes without requiring pointer alignment.
[[gnu::always_inline]] static inline uint64_t
load64(unsigned char const *const p)
{
    uint64_t v;
    __builtin_memcpy(&v, p, sizeof v);
    return v;
}

    #ifdef MONAD_ZKVM_KECCAK_TEST
// Software permutation supplied by the host tests.
extern "C" void test_keccak_f(uint64_t (*state)[25]);
    #endif

extern "C"
{

// Inline ZisK's Keccak-f marker (CSR 0x800) to avoid call/return overhead.
// The precompile updates state in place; the memory clobber tells the
// compiler that this instruction reads and writes memory.
[[gnu::always_inline]] inline void zisk_keccakf(uint64_t (*state)[25]) noexcept
{
    #ifdef MONAD_ZKVM_ZISK
    asm volatile(".option push\n\t"
                 ".option arch, +zicsr\n\t"
                 "csrs 0x800, %0\n\t"
                 ".option pop"
                 :
                 : "r"(state)
                 : "memory");
    #else
    // Host tests supply a software permutation; the sponge stays unchanged.
    test_keccak_f(state);
    #endif
}

static inline void keccak_permute(uint64_t (*state)[25])
{
    zisk_keccakf(state);
}

void monad_zkvm_keccak256_fast(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17

    // 200 bytes: rate in st[0..16], capacity in st[17..24].
    uint64_t st[25];
    // Skip 17 words (136 bytes) and zero only the 64-byte capacity.
    std::memset(st + WORDS, 0, sizeof(st) - KECCAK_RATE);
    if (len < KECCAK_RATE) {
        // Short inputs leave bytes untouched; zero the rate before padding.
        std::memset(st, 0, KECCAK_RATE);
    }
    auto const *p = static_cast<unsigned char const *>(in);

    // With -mtune=size, load64 becomes one ld, even for unaligned input.
    // Copy the first block into the rate; XOR subsequent blocks.
    // -mzisk-dma lowers the copy to ZisK's block-move precompile.
    bool first = true;
    while (len >= KECCAK_RATE) {
        if (first) {
            // Initialize all 136 rate bytes before the first permutation.
            std::memcpy(st, p, KECCAK_RATE);
            first = false;
        }
        else {
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= load64(p + 8 * i);
            }
        }
        keccak_permute(&st);
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }

    // Final block: remainder plus pad10*1 with the 0x01 domain byte.
    if (first) {
        // No full block was absorbed; pad directly in the zeroed state.
        if (len) {
            std::memcpy(st, p, len);
        }
        auto *const b = reinterpret_cast<unsigned char *>(st);
        b[len] = 0x01;
        // Set the final padding bit through aligned lane 16 (byte 135).
        static_assert(KECCAK_RATE - 1 == 16 * 8 + 7);
        st[16] |= uint64_t{0x80} << 56;
    }
    else {
        alignas(8) unsigned char last[KECCAK_RATE] = {};
        if (len) {
            std::memcpy(last, p, len);
        }
        last[len] = 0x01;
        // Skip trailing zero lanes; fixed counts preserve loop unrolling.
        // A runtime count measured worse.
        if (len <= 31) {
            for (size_t i = 0; i < 4; ++i) {
                st[i] ^= load64(last + 8 * i);
            }
        }
        else if (len <= 63) {
            for (size_t i = 0; i < 8; ++i) {
                st[i] ^= load64(last + 8 * i);
            }
        }
        else if (len <= 95) {
            for (size_t i = 0; i < 12; ++i) {
                st[i] ^= load64(last + 8 * i);
            }
        }
        else if (len <= 127) {
            for (size_t i = 0; i < 16; ++i) {
                st[i] ^= load64(last + 8 * i);
            }
        }
        else {
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= load64(last + 8 * i);
            }
        }
        // Fold the final padding bit directly into the state, avoiding
        // a byte read-modify-write in last.
        st[16] ^= uint64_t{0x80} << 56;
    }
    keccak_permute(&st);

    std::memcpy(out, st, 32);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_KECCAK_TEST
