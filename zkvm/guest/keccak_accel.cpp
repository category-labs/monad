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
constexpr size_t KECCAK_CAPACITY_BYTES = 64;

// Load eight bytes without requiring pointer alignment.
[[gnu::always_inline]] static inline uint64_t
load64(unsigned char const *const bytes)
{
    uint64_t word;
    __builtin_memcpy(&word, bytes, sizeof word);
    return word;
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

    // Enabled by default on ZisK; setting this to 0 removes the table and
    // lookup path. The lookups are ZisK executor calls, so other builds go
    // without it.
    #ifndef MONAD_ZKVM_KECCAKF_MEMO
        #ifdef MONAD_ZKVM_ZISK
            #define MONAD_ZKVM_KECCAKF_MEMO 1
        #else
            #define MONAD_ZKVM_KECCAKF_MEMO 0
        #endif
    #endif
    #if MONAD_ZKVM_KECCAKF_MEMO && !defined(MONAD_ZKVM_ZISK)
        #error "the Keccak-f memo needs the ZisK executor"
    #endif

    #if MONAD_ZKVM_KECCAKF_MEMO

// Executor hints avoid guest-side searches over 200-byte states.
// Accept only index < used and an exact match against an owned input copy.
// Cached outputs come from real permutations in this execution.
// Publish each entry only after both states are written.
constexpr size_t KECCAKF_LANES = 25;
constexpr size_t KECCAKF_STATE_BYTES = KECCAKF_LANES * sizeof(uint64_t);

// Append-only table: 2^18 entries of 400 bytes use 100 MiB of .bss.
// Entries are never evicted; a full table computes misses without caching them.
struct alignas(8) KeccakfEntry
{
    uint64_t in[KECCAKF_LANES]; // the state before the permutation
    uint64_t out[KECCAKF_LANES]; // and after it
};

static_assert(
    sizeof(KeccakfEntry) == 2 * KECCAKF_STATE_BYTES,
    "an entry is exactly the two states");

constexpr size_t KECCAKF_MEMO_ENTRIES = size_t{1} << 18;

static KeccakfEntry keccakf_memo[KECCAKF_MEMO_ENTRIES];
static uint64_t keccakf_memo_used = 0;

        // Preserve constant lengths with -mzisk-dma for inline DMA lowering.
        // Otherwise hide the length to retain library calls instead of
        // expanding copies and comparisons into per-word operations.
        #ifdef MONAD_ZKVM_ZISK_DMA_LOWERING
            #define MONAD_KECCAKF_LEN(n) (n)
        #else
static inline size_t keccakf_opaque(size_t length)
{
    asm("" : "+r"(length));
    return length;
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

// Push a value via 0x8F0 or a 25-word state via 0x8F8, invoke the fcall
// via 0x8C0, then read its result at 0xFFE. Let the compiler choose the
// register to avoid unnecessary moves. The "r" constraint keeps even
// zero values out of x0, which ZisK treats as a no-op instead of a push.
constexpr uint64_t KECCAKF_INDEX_NOT_FOUND = ~uint64_t{0};

// Associate `index` with the next permutation's input.
// No other Keccak-f call may intervene.
static inline void fcall_set_keccakf_index(uint64_t const index)
{
    asm volatile("csrs 0x8F0, %0\n\t" // one parameter, by value
                 "csrwi 0x8C0, 24" // FCALL_SET_KECCAKF_CACHE_INDEX_ID
                 :
                 : "r"(index)
                 : "memory");
}

// Return an untrusted hint index, or KECCAKF_INDEX_NOT_FOUND.
// The caller must check the index and compare the complete input state.
static inline uint64_t fcall_get_keccakf_index(uint64_t const *const state)
{
    uint64_t index;
    asm volatile("csrs 0x8F8, %[state]\n\t" // one parameter: 25 words at state
                 "csrwi 0x8C0, 25\n\t" // FCALL_GET_KECCAKF_CACHE_INDEX_ID
                 "csrr %[index], 0xFFE" // fcall_get: the index
                 : [index] "=&r"(index)
                 : [state] "r"(state)
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

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_KECCAK_TEST
