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

// Load eight bytes without requiring pointer alignment.
[[gnu::always_inline]] static inline uint64_t
load64(unsigned char const *const p)
{
    uint64_t v;
    __builtin_memcpy(&v, p, sizeof v);
    return v;
}

// ziskos's raw Keccak-f[1600] precompile entry.
extern "C" void syscall_keccak_f(uint64_t (*state)[25]);

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

// Executor hints avoid guest-side searches over 200-byte states.
// Accept only index < used and an exact match against an owned input copy.
// Cached outputs come from real permutations in this execution.
// Advance the local used count after both states are written;
// save it globally when the digest completes.
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

// Extra scratch entry for short inputs when the table is full.
// It is never published, so a hint cannot select it.
static KeccakfEntry keccakf_memo[KECCAKF_MEMO_ENTRIES + 1];
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

// Associate `index` with the next permutation's input.
// No other Keccak-f call may intervene.
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

// Build a padded input (< KECCAK_RATE bytes) in the next memo entry.
// Hints must name a published entry with an exact input match; this scratch
// stays unpublished until both states are ready.
// Its input starts zeroed: misses advance to fresh .bss, hits clear the
// rate, and full-table calls clear all 200 bytes after permutation.
static void keccak256_one_block(
    void const *const in, size_t const len, uint8_t out[32])
{
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");

    // Keep the count local to avoid global reloads after asm memory clobbers.
    uint64_t const used = keccakf_memo_used;
    KeccakfEntry &e = keccakf_memo[used];
    uint64_t *const s = e.in;

    if (len) {
        std::memcpy(s, in, len);
    }
    reinterpret_cast<unsigned char *>(s)[len] = 0x01;
    s[16] |= uint64_t{0x80} << 56;

    uint64_t const index = fcall_get_keccakf_index(s);
    if (index < used && keccakf_state_eq(keccakf_memo[index].in, s)) {
        std::memcpy(out, keccakf_memo[index].out, 32);
        // Clear 17 lanes (136 bytes) used by input and padding.
        // No permutation ran here, so the other 64 bytes are still zero.
        std::memset(s, 0, KECCAK_RATE);
        return;
    }

    if (used == KECCAKF_MEMO_ENTRIES) {
        // Full table: permute the spare slot, then clear it for reuse.
        zisk_keccakf(&e.in);
        std::memcpy(out, s, 32);
        std::memset(s, 0, KECCAKF_STATE_BYTES);
        return;
    }

    // Preserve `in`; copy only the rate to `out` for the permutation.
    // Both capacities are zero: this is the first block and `out` is unused.
    std::memcpy(e.out, s, 17 * sizeof(uint64_t));
    fcall_set_keccakf_index(used);
    zisk_keccakf(&e.out);
    // Publish only after both input and output are stored.
    keccakf_memo_used = used + 1;
    std::memcpy(out, e.out, 32);
}

// Permute pre = keccakf_memo[used].in without changing it.
// A hit requires a valid index and an exact full-state match.
// First allows a rate-only copy into a fresh output (both capacities zero).
// Later blocks and the reused spare require all 200 bytes.
// Lookup=false still computes the result and caches it if space permits.
// A miss returns pre + KECCAKF_LANES; a hit returns an earlier entry's output.
// The caller writes the local count back after the digest.
template <bool First, bool Lookup = true>
static inline uint64_t const *
keccakf_memo_permute(uint64_t *const pre, uint64_t &used)
{
    if constexpr (Lookup) {
        uint64_t const index = fcall_get_keccakf_index(pre);
        // Reject out-of-range hints before reading the table.
        if (index < used && keccakf_state_eq(keccakf_memo[index].in, pre)) {
            return keccakf_memo[index].out;
        }
    }
    uint64_t *const slot_out = pre + KECCAKF_LANES;
    auto *const post = reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(slot_out);
    if (used == KECCAKF_MEMO_ENTRIES) {
        // The reused spare may hold an earlier output; overwrite all lanes.
        keccakf_state_copy(slot_out, pre);
        zisk_keccakf(post);
        return slot_out;
    }
    if constexpr (First) {
        std::memcpy(slot_out, pre, 17 * sizeof(uint64_t));
    }
    else {
        keccakf_state_copy(slot_out, pre);
    }
    // Associate this slot with the next permutation; keep these calls adjacent.
    fcall_set_keccakf_index(used);
    zisk_keccakf(post);
    // Publish only after both input and output are stored.
    ++used;
    return slot_out;
}

// Inputs >= 136 bytes: build states directly in the memo, carrying the
// previous output's 64-byte capacity. The scratch is zero on entry;
// later blocks overwrite all 25 lanes.
static void keccak256_memo_sponge(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
    auto const *p = static_cast<unsigned char const *>(in);
    // Keep the count local across permutations; write it back once on return.
    uint64_t used = keccakf_memo_used;

    // Copy misaligned inputs that fit here once, making word loads aligned.
    alignas(8) unsigned char staged[8 * KECCAK_RATE];
    if ((reinterpret_cast<uintptr_t>(p) & 7) != 0 && len <= sizeof(staged)) {
        std::memcpy(staged, p, len);
        p = staged;
    }

    uint64_t *pre = keccakf_memo[used].in;
    std::memcpy(pre, p, KECCAK_RATE);
    p += KECCAK_RATE;
    len -= KECCAK_RATE;
    uint64_t const *post = keccakf_memo_permute<true>(pre, used);

    // Stop lookups after the first miss. This may forgo later hits, but
    // skipped lookups run the real permutation and cache it when space permits.
    bool look = post != pre + KECCAKF_LANES;
    while (look && len >= KECCAK_RATE) {
        pre = keccakf_memo[used].in;
        // Keep one opaque base pointer for the lanes to avoid extra saved
        // registers for their addresses.
        asm("" : "+r"(pre));
        for (size_t i = 0; i < WORDS; ++i) {
            pre[i] = post[i] ^ load64(p + 8 * i);
        }
        std::memcpy(pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
        post = keccakf_memo_permute<false>(pre, used);
        look = post != pre + KECCAKF_LANES;
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }
    while (len >= KECCAK_RATE) {
        pre = keccakf_memo[used].in;
        asm("" : "+r"(pre));
        for (size_t i = 0; i < WORDS; ++i) {
            pre[i] = post[i] ^ load64(p + 8 * i);
        }
        std::memcpy(pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
        post = keccakf_memo_permute<false, false>(pre, used);
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }

    // Absorb the remaining bytes and Keccak padding (0x01 ... 0x80).
    // The partial lane is read backwards from the input end; the preceding
    // full block keeps the eight-byte load within the input.
    pre = keccakf_memo[used].in;
    size_t const whole = len / 8;
    unsigned const rem = static_cast<unsigned>(len % 8);
    // Direct label addresses avoid switch-table offset arithmetic.
    // len < KECCAK_RATE guarantees whole is in [0, 16].
    static void *const entry[] = {
        &&lanes0,  &&lanes1,  &&lanes2,  &&lanes3,  &&lanes4,  &&lanes5,
        &&lanes6,  &&lanes7,  &&lanes8,  &&lanes9,  &&lanes10, &&lanes11,
        &&lanes12, &&lanes13, &&lanes14, &&lanes15, &&lanes16};
    static_assert(sizeof(entry) / sizeof(entry[0]) == WORDS);
    goto *entry[whole];
lanes16:
    pre[15] = post[15] ^ load64(p + 120);
lanes15:
    pre[14] = post[14] ^ load64(p + 112);
lanes14:
    pre[13] = post[13] ^ load64(p + 104);
lanes13:
    pre[12] = post[12] ^ load64(p + 96);
lanes12:
    pre[11] = post[11] ^ load64(p + 88);
lanes11:
    pre[10] = post[10] ^ load64(p + 80);
lanes10:
    pre[9] = post[9] ^ load64(p + 72);
lanes9:
    pre[8] = post[8] ^ load64(p + 64);
lanes8:
    pre[7] = post[7] ^ load64(p + 56);
lanes7:
    pre[6] = post[6] ^ load64(p + 48);
lanes6:
    pre[5] = post[5] ^ load64(p + 40);
lanes5:
    pre[4] = post[4] ^ load64(p + 32);
lanes4:
    pre[3] = post[3] ^ load64(p + 24);
lanes3:
    pre[2] = post[2] ^ load64(p + 16);
lanes2:
    pre[1] = post[1] ^ load64(p + 8);
lanes1:
    pre[0] = post[0] ^ load64(p);
lanes0:
    uint64_t lane = uint64_t{0x01} << (8 * rem);
    if (rem != 0) {
        lane |= load64(p + len - 8) >> (8 * (8 - rem));
    }
    pre[whole] = post[whole] ^ lane;
    std::memcpy(
        pre + whole + 1, post + whole + 1, (KECCAKF_LANES - 1 - whole) * 8);
    pre[16] ^= uint64_t{0x80} << 56;
    post = look ? keccakf_memo_permute<false>(pre, used)
                : keccakf_memo_permute<false, false>(pre, used);
    std::memcpy(out, post, 32);

    // A hit or full table reuses this scratch; a miss advanced to a zero slot.
    if (pre == keccakf_memo[used].in) {
        std::memset(pre, 0, KECCAKF_STATE_BYTES);
    }
    keccakf_memo_used = used;
}

#endif // MONAD_ZKVM_KECCAKF_MEMO

// Raw permutation for the sponge's non-memo path.
static inline void keccak_permute(uint64_t (*state)[25])
{
    zisk_keccakf(state);
}

extern "C" void monad_zkvm_keccak256_fast(
    void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17

#if MONAD_ZKVM_KECCAKF_MEMO
    // Short inputs build their padded state directly in the memo.
    if (len < KECCAK_RATE) {
        keccak256_one_block(in, len, out);
    }
    else {
        keccak256_memo_sponge(in, len, out);
    }
    return;
#endif

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
        auto const *const w = reinterpret_cast<uint64_t const *>(last);
        // Skip trailing zero lanes; fixed counts preserve loop unrolling.
        // A runtime count measured worse.
        if (len <= 31) {
            for (size_t i = 0; i < 4; ++i) {
                st[i] ^= w[i];
            }
        }
        else if (len <= 63) {
            for (size_t i = 0; i < 8; ++i) {
                st[i] ^= w[i];
            }
        }
        else if (len <= 95) {
            for (size_t i = 0; i < 12; ++i) {
                st[i] ^= w[i];
            }
        }
        else if (len <= 127) {
            for (size_t i = 0; i < 16; ++i) {
                st[i] ^= w[i];
            }
        }
        else {
            for (size_t i = 0; i < WORDS; ++i) {
                st[i] ^= w[i];
            }
        }
        // Fold the final padding bit directly into the state, avoiding
        // a byte read-modify-write in last.
        st[16] ^= uint64_t{0x80} << 56;
    }
    keccak_permute(&st);

    std::memcpy(out, st, 32);
}

#endif // MONAD_ZKVM_ZISK
