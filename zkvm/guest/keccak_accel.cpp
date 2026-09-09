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
// Keccak-f precompile. Buffer the final block for Ethereum's 0x01/0x80 padding.

#ifdef MONAD_ZKVM_ZISK

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

extern "C"
{

// ziskos's raw Keccak-f[1600] precompile entry.
void syscall_keccak_f(uint64_t (*state)[25]);

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

void monad_zkvm_keccak256_fast(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17

    uint64_t st[25] = {};
    auto const *p = static_cast<unsigned char const *>(in);

    // With -mtune=size, load64 becomes one ld, even for unaligned input.
    // ZisK supports these loads directly, avoiding shifts and a block copy.
    while (len >= KECCAK_RATE) {
        for (size_t i = 0; i < WORDS; ++i) {
            st[i] ^= load64(p + 8 * i);
        }
        keccak_permute(&st);
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }

    // Final block: remainder plus pad10*1 with the 0x01 domain byte.
    alignas(8) unsigned char last[KECCAK_RATE] = {};
    if (len) {
        std::memcpy(last, p, len);
    }
    last[len] = 0x01;
    last[KECCAK_RATE - 1] |= 0x80;
    auto const *const w = reinterpret_cast<uint64_t const *>(last);
    for (size_t i = 0; i < WORDS; ++i) {
        st[i] ^= w[i];
    }
    keccak_permute(&st);

    std::memcpy(out, st, 32);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK
