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

// Enabled by default; setting this to 0 removes the table and lookup path.
#ifndef MONAD_ZKVM_KECCAKF_MEMO
    #define MONAD_ZKVM_KECCAKF_MEMO 1
#endif

#if MONAD_ZKVM_KECCAKF_MEMO

// Executor hints avoid a guest-side lookup over 200-byte states.
// Hints are untrusted: accept only an index below keccakf_memo_used and an
// exact input match. Cached outputs come from real permutations in this run.
// Entries own both states, since callers reuse and mutate their buffers;
// publish each entry only after both states are written.
constexpr size_t KECCAKF_LANES = 25;
constexpr size_t KECCAKF_STATE_BYTES = KECCAKF_LANES * sizeof(uint64_t);

// Append-only table: 2^18 entries of 512 bytes use 128 MiB of .bss.
// Entries are never evicted; a full table computes misses without caching them.
// Two 200-byte states are padded to 512 bytes so indexing is a shift, not a
// multiply; the padding is never read or written.
struct alignas(8) KeccakfEntry
{
    uint64_t in[KECCAKF_LANES]; // the state before the permutation
    uint64_t out[KECCAKF_LANES]; // and after it
    uint64_t pad[64 - 2 * KECCAKF_LANES];
};

static_assert(
    sizeof(KeccakfEntry) == 512 && sizeof(KeccakfEntry) > 2 * KECCAKF_STATE_BYTES,
    "an entry is the two states, padded to a shift");

constexpr size_t KECCAKF_MEMO_ENTRIES = size_t{1} << 18;

static KeccakfEntry keccakf_memo[KECCAKF_MEMO_ENTRIES];
static uint64_t keccakf_memo_used = 0;

// Preserve constant lengths with -mzisk-dma for inline DMA lowering.
// Otherwise hide the length to retain library calls instead of expanding
// copies and comparisons into per-word operations.
#ifdef MONAD_ZKVM_ZISK_DMA_LOWERING
    #define MONAD_KECCAKF_LEN(n) (n)
#else
static inline size_t keccakf_opaque(size_t n)
{
    asm("" : "+r"(n));
    return n;
}
    #define MONAD_KECCAKF_LEN(n) keccakf_opaque(n)
#endif

static inline bool keccakf_state_eq(uint64_t const *a, uint64_t const *b)
{
    return std::memcmp(a, b, MONAD_KECCAKF_LEN(KECCAKF_STATE_BYTES)) == 0;
}

static inline void keccakf_state_copy(uint64_t *dst, uint64_t const *src)
{
    std::memcpy(dst, src, MONAD_KECCAKF_LEN(KECCAKF_STATE_BYTES));
}

// Pass parameters via 0x8F0 (value) or 0x8F8 (25-word state), invoke the
// fcall via 0x8C0, and read its result at 0xFFE. Pin parameters to a0:
// ZisK treats a parameter push using x0 as a no-op.
constexpr uint64_t KECCAKF_INDEX_NOT_FOUND = ~uint64_t{0};

// File the input state of the NEXT permutation under `index`.
static inline void fcall_set_keccakf_index(uint64_t const index)
{
    register unsigned long a0 asm("a0") = static_cast<unsigned long>(index);
    asm volatile("csrs 0x8F0, %0\n\t" // one parameter, by value
                 "csrwi 0x8C0, 24" // FCALL_SET_KECCAKF_CACHE_INDEX_ID
                 :
                 : "r"(a0)
                 : "memory");
}

// The index `state` was filed under, or KECCAKF_INDEX_NOT_FOUND.
static inline uint64_t fcall_get_keccakf_index(uint64_t const *const state)
{
    register unsigned long a0 asm("a0") =
        reinterpret_cast<unsigned long>(state);
    uint64_t index;
    asm volatile("csrs 0x8F8, %[st]\n\t" // one parameter: 25 words at [st]
                 "csrwi 0x8C0, 25\n\t" // FCALL_GET_KECCAKF_CACHE_INDEX_ID
                 "csrr %[idx], 0xFFE" // fcall_get: the index
                 : [idx] "=&r"(index)
                 : [st] "r"(a0)
                 : "memory");
    return index;
}

#endif // MONAD_ZKVM_KECCAKF_MEMO

// Reuse a validated result when available; otherwise run Keccak-f.
static inline void keccak_permute(uint64_t (*state)[25])
{
#if MONAD_ZKVM_KECCAKF_MEMO
    uint64_t *const s = &(*state)[0];
    uint64_t const index = fcall_get_keccakf_index(s);

    // Reject out-of-range hints, including NOT_FOUND, before reading the table.
    if (index < keccakf_memo_used &&
        keccakf_state_eq(keccakf_memo[index].in, s)) {
        keccakf_state_copy(s, keccakf_memo[index].out);
        return;
    }

    if (keccakf_memo_used == KECCAKF_MEMO_ENTRIES) {
        // Full table: compute without caching another entry.
        zisk_keccakf(state);
        return;
    }

    // Register this slot for the next Keccak-f call; no other permutation
    // may intervene between fcall_set_keccakf_index and zisk_keccakf.
    KeccakfEntry &e = keccakf_memo[keccakf_memo_used];
    keccakf_state_copy(e.in, s);
    fcall_set_keccakf_index(keccakf_memo_used);
    zisk_keccakf(state);
    keccakf_state_copy(e.out, s);
    // Publish only after both input and output are stored.
    ++keccakf_memo_used;
#else
    zisk_keccakf(state);
#endif
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
