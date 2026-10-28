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

    #include <category/core/likely.h>

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
// Software permutation and executor hints supplied by the host tests.
extern "C" void test_keccak_f(uint64_t (*state)[25]);
void test_set_keccakf_index(uint64_t index);
uint64_t test_get_keccakf_index(uint64_t const *state);
    #endif

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
    #if MONAD_ZKVM_KECCAKF_MEMO && !defined(MONAD_ZKVM_ZISK) &&                \
        !defined(MONAD_ZKVM_KECCAK_TEST)
        #error "the Keccak-f memo needs the ZisK executor"
    #endif

    #if MONAD_ZKVM_KECCAKF_MEMO

// Executor hints avoid guest-side searches over 200-byte states.
// Accept only index < used and an exact match against an owned input copy.
// Cached outputs come from real permutations in this execution.
// Advance the local used count after both states are written;
// save it globally when the digest completes.
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

        #if defined(MONAD_ZKVM_KECCAK_TEST) && !defined(MONAD_ZKVM_ZISK)
// Reach the full-table fallback in host tests.
constexpr size_t KECCAKF_MEMO_ENTRIES = 16;
        #else
constexpr size_t KECCAKF_MEMO_ENTRIES = size_t{1} << 18;
        #endif

// Extra scratch entry for uncached permutations when the table is full.
// It is never published, so a hint cannot select it.
static KeccakfEntry keccakf_memo[KECCAKF_MEMO_ENTRIES + 1];
static uint64_t keccakf_memo_used = 0;

    // Preserve constant lengths with -mzisk-dma for inline DMA lowering.
    // Otherwise hide the length to retain library calls instead of expanding
    // copies and comparisons into per-word operations.
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
        #ifdef MONAD_ZKVM_ZISK
    asm volatile("csrs 0x8F0, %0\n\t" // one parameter, by value
                 "csrwi 0x8C0, 24" // FCALL_SET_KECCAKF_CACHE_INDEX_ID
                 :
                 : "r"(index)
                 : "memory");
        #else
    test_set_keccakf_index(index);
        #endif
}

// Return an untrusted hint index, or KECCAKF_INDEX_NOT_FOUND.
// The caller must check the index and compare the complete input state.
static inline uint64_t fcall_get_keccakf_index(uint64_t const *const state)
{
        #ifdef MONAD_ZKVM_ZISK
    uint64_t index;
    asm volatile("csrs 0x8F8, %[state]\n\t" // one parameter: 25 words at state
                 "csrwi 0x8C0, 25\n\t" // FCALL_GET_KECCAKF_CACHE_INDEX_ID
                 "csrr %[index], 0xFFE" // fcall_get: the index
                 : [index] "=&r"(index)
                 : [state] "r"(state)
                 : "memory");
    return index;
        #else
    return test_get_keccakf_index(state);
        #endif
}

// Build a padded input (< KECCAK_RATE bytes) in the next memo entry.
// Hints must name a published entry with an exact input match; this scratch
// stays unpublished until both states are ready.
// Its input starts zeroed: misses advance to fresh .bss, hits clear the
// rate, and full-table calls clear all 200 bytes after permutation.
static void keccak256_one_block(
    void const *const input, size_t const input_length, uint8_t output[32])
{
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");

    // Keep the count local to avoid global reloads after asm memory clobbers.
    uint64_t const entry_count = keccakf_memo_used;
    KeccakfEntry &entry = keccakf_memo[entry_count];
    uint64_t *const state = entry.in;

    if (input_length) {
        std::memcpy(state, input, input_length);
    }
    reinterpret_cast<unsigned char *>(state)[input_length] = 0x01;
    state[16] |= uint64_t{0x80} << 56;

    uint64_t const index = fcall_get_keccakf_index(state);
    if (index < entry_count &&
        keccakf_state_eq(keccakf_memo[index].in, state)) {
        std::memcpy(output, keccakf_memo[index].out, 32);
        // Clear 17 lanes (136 bytes) used by input and padding.
        // No permutation ran here, so the other 64 bytes are still zero.
        std::memset(state, 0, KECCAK_RATE);
        return;
    }

    if (entry_count == KECCAKF_MEMO_ENTRIES) {
        // Full table: permute the spare slot, then clear it for reuse.
        zisk_keccakf(&entry.in);
        std::memcpy(output, state, 32);
        std::memset(state, 0, KECCAKF_STATE_BYTES);
        return;
    }

    // Preserve `in`; copy only the rate to `out` for the permutation.
    // Both capacities are zero: this is the first block and `out` is unused.
    std::memcpy(entry.out, state, 17 * sizeof(uint64_t));
    fcall_set_keccakf_index(entry_count);
    zisk_keccakf(&entry.out);
    // Publish only after both input and output are stored.
    keccakf_memo_used = entry_count + 1;
    std::memcpy(output, entry.out, 32);
}

// Permute input_state = keccakf_memo[entry_count].in without changing it.
// A hit requires a valid index and an exact full-state match.
// First allows a rate-only copy into a fresh output (both capacities zero).
// Later blocks and the reused spare require all 200 bytes.
// Lookup=false still computes the result and caches it if space permits.
// A miss returns input_state + KECCAKF_LANES; a hit returns an earlier entry's
// output. The caller writes the local count back after the digest.
template <bool First, bool Lookup = true>
static inline uint64_t const *
keccakf_memo_permute(uint64_t *const input_state, uint64_t &entry_count)
{
    if constexpr (Lookup) {
        uint64_t const index = fcall_get_keccakf_index(input_state);
        // Reject out-of-range hints before reading the table.
        if (index < entry_count &&
            keccakf_state_eq(keccakf_memo[index].in, input_state)) {
            return keccakf_memo[index].out;
        }
    }
    uint64_t *const output_lanes = input_state + KECCAKF_LANES;
    auto *const output_state =
        reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(output_lanes);
    if (entry_count == KECCAKF_MEMO_ENTRIES) {
        // The reused spare may hold an earlier output; overwrite all lanes.
        keccakf_state_copy(output_lanes, input_state);
        zisk_keccakf(output_state);
        return output_lanes;
    }
    if constexpr (First) {
        std::memcpy(output_lanes, input_state, 17 * sizeof(uint64_t));
    }
    else {
        keccakf_state_copy(output_lanes, input_state);
    }
    // Associate this slot with the next permutation; keep these calls adjacent.
    fcall_set_keccakf_index(entry_count);
    zisk_keccakf(output_state);
    // Publish only after both input and output are stored.
    ++entry_count;
    return output_lanes;
}

// Inputs >= 136 bytes: build states directly in the memo, carrying the
// previous output's 64-byte capacity. The scratch is zero on entry;
// later blocks overwrite all 25 lanes.
static void keccak256_memo_sponge(
    void const *const input, size_t remaining_bytes, uint8_t output[32])
{
    constexpr size_t RATE_WORDS = KECCAK_RATE / 8; // 17
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
    auto const *input_cursor = static_cast<unsigned char const *>(input);
    // Keep the count local across permutations; write it back once on return.
    uint64_t entry_count = keccakf_memo_used;

    // Copy misaligned inputs that fit here once, making word loads aligned.
    alignas(8) unsigned char aligned_input[8 * KECCAK_RATE];
    if ((reinterpret_cast<uintptr_t>(input_cursor) & 7) != 0 &&
        remaining_bytes <= sizeof(aligned_input)) {
        std::memcpy(aligned_input, input_cursor, remaining_bytes);
        input_cursor = aligned_input;
    }

    uint64_t *input_state = keccakf_memo[entry_count].in;
    std::memcpy(input_state, input_cursor, KECCAK_RATE);
    input_cursor += KECCAK_RATE;
    remaining_bytes -= KECCAK_RATE;
    uint64_t const *output_state =
        keccakf_memo_permute<true>(input_state, entry_count);

    // Stop lookups after the first miss. This may forgo later hits, but
    // skipped lookups run the real permutation and cache it when space permits.
    bool keep_looking_up = output_state != input_state + KECCAKF_LANES;

    // Full branch RLP: 3 header bytes + 16 * (1 prefix + 32 hash bytes)
    // + 1 empty-value byte = 532 bytes.
    // After a first-block miss, absorb its remaining 2 * 136 + 124 bytes
    // with fixed offsets and padding. Require three free memo slots;
    // otherwise use the general path below.
    constexpr size_t FULL_BRANCH_RLP_BYTES = 532;
    static_assert(
        FULL_BRANCH_RLP_BYTES - KECCAK_RATE == 2 * KECCAK_RATE + 15 * 8 + 4,
        "two middle blocks, then fifteen lanes and four bytes");
    if (MONAD_LIKELY(!keep_looking_up) &&
        remaining_bytes == FULL_BRANCH_RLP_BYTES - KECCAK_RATE &&
        entry_count + 3 <= KECCAKF_MEMO_ENTRIES) {
        // One opaque base for the three slots keeps every lane at a literal
        // offset from a single register.
        KeccakfEntry *entries = &keccakf_memo[entry_count];
        asm("" : "+r"(entries));
        // Block 2: input_cursor follows block 1; output_state is its
        // permutation result. XOR the 136 input bytes into the state's first 17
        // lanes.
        for (size_t i = 0; i < RATE_WORDS; ++i) {
            entries[0].in[i] = output_state[i] ^ load64(input_cursor + 8 * i);
        }
        // Preserve the eight capacity lanes, which do not absorb input.
        std::memcpy(
            entries[0].in + RATE_WORDS,
            output_state + RATE_WORDS,
            (KECCAKF_LANES - RATE_WORDS) * 8);
        // Keep .in for future cache comparisons; permute its copy in .out.
        // Register each entry immediately before computing its permutation.
        keccakf_state_copy(entries[0].out, entries[0].in);
        fcall_set_keccakf_index(entry_count);
        zisk_keccakf(&entries[0].out);

        // Block 3: repeat absorption using block 2's output state.
        unsigned char const *const third_block = input_cursor + KECCAK_RATE;
        for (size_t i = 0; i < RATE_WORDS; ++i) {
            entries[1].in[i] = entries[0].out[i] ^ load64(third_block + 8 * i);
        }
        std::memcpy(
            entries[1].in + RATE_WORDS,
            entries[0].out + RATE_WORDS,
            (KECCAKF_LANES - RATE_WORDS) * 8);
        keccakf_state_copy(entries[1].out, entries[1].in);
        fcall_set_keccakf_index(entry_count + 1);
        zisk_keccakf(&entries[1].out);

        // Final block: 124 bytes = fifteen complete lanes + four bytes.
        unsigned char const *const final_block = input_cursor + 2 * KECCAK_RATE;
        for (size_t i = 0; i < 15; ++i) {
            entries[2].in[i] = entries[1].out[i] ^ load64(final_block + 8 * i);
        }
        // Read exactly four bytes to stay within the input. In byte order:
        // lane 15 = [last four bytes, 01, 00, 00, 00];
        // lane 16 = [00, 00, 00, 00, 00, 00, 00, 80].
        uint32_t final_four_bytes;
        __builtin_memcpy(
            &final_four_bytes, final_block + 15 * 8, sizeof final_four_bytes);
        entries[2].in[15] =
            entries[1].out[15] ^ (final_four_bytes | uint64_t{0x01} << 32);
        entries[2].in[16] = entries[1].out[16] ^ (uint64_t{0x80} << 56);
        std::memcpy(
            entries[2].in + RATE_WORDS,
            entries[1].out + RATE_WORDS,
            (KECCAKF_LANES - RATE_WORDS) * 8);
        keccakf_state_copy(entries[2].out, entries[2].in);
        fcall_set_keccakf_index(entry_count + 2);
        zisk_keccakf(&entries[2].out);
        // Keccak-256 returns the first 32 bytes of the final state.
        std::memcpy(output, entries[2].out, 32);
        // Publish all three entries; the next scratch slot is still unwritten.
        keccakf_memo_used = entry_count + 3;
        return;
    }

    while (keep_looking_up && remaining_bytes >= KECCAK_RATE) {
        input_state = keccakf_memo[entry_count].in;
        // Keep one opaque base pointer for the lanes to avoid extra saved
        // registers for their addresses.
        asm("" : "+r"(input_state));
        for (size_t i = 0; i < RATE_WORDS; ++i) {
            input_state[i] = output_state[i] ^ load64(input_cursor + 8 * i);
        }
        std::memcpy(
            input_state + RATE_WORDS,
            output_state + RATE_WORDS,
            (KECCAKF_LANES - RATE_WORDS) * 8);
        output_state = keccakf_memo_permute<false>(input_state, entry_count);
        keep_looking_up = output_state != input_state + KECCAKF_LANES;
        input_cursor += KECCAK_RATE;
        remaining_bytes -= KECCAK_RATE;
    }
    while (remaining_bytes >= KECCAK_RATE) {
        input_state = keccakf_memo[entry_count].in;
        asm("" : "+r"(input_state));
        for (size_t i = 0; i < RATE_WORDS; ++i) {
            input_state[i] = output_state[i] ^ load64(input_cursor + 8 * i);
        }
        std::memcpy(
            input_state + RATE_WORDS,
            output_state + RATE_WORDS,
            (KECCAKF_LANES - RATE_WORDS) * 8);
        output_state =
            keccakf_memo_permute<false, false>(input_state, entry_count);
        input_cursor += KECCAK_RATE;
        remaining_bytes -= KECCAK_RATE;
    }

    // Absorb the remaining bytes and Keccak padding (0x01 ... 0x80).
    // The partial lane is read backwards from the input end; the preceding
    // full block keeps the eight-byte load within the input.
    input_state = keccakf_memo[entry_count].in;
    size_t const full_tail_lanes = remaining_bytes / 8;
    unsigned const partial_lane_bytes =
        static_cast<unsigned>(remaining_bytes % 8);
    // Enter the unrolled tail at its number of complete lanes.
    // Each label falls through to absorb the preceding lane.
    // remaining_bytes < KECCAK_RATE guarantees full_tail_lanes is in [0, 16].
    static void *const tail_lane_labels[] = {
        &&lanes0,
        &&lanes1,
        &&lanes2,
        &&lanes3,
        &&lanes4,
        &&lanes5,
        &&lanes6,
        &&lanes7,
        &&lanes8,
        &&lanes9,
        &&lanes10,
        &&lanes11,
        &&lanes12,
        &&lanes13,
        &&lanes14,
        &&lanes15,
        &&lanes16};
    static_assert(
        sizeof(tail_lane_labels) / sizeof(tail_lane_labels[0]) == RATE_WORDS);
    goto *tail_lane_labels[full_tail_lanes];
lanes16:
    input_state[15] = output_state[15] ^ load64(input_cursor + 120);
lanes15:
    input_state[14] = output_state[14] ^ load64(input_cursor + 112);
lanes14:
    input_state[13] = output_state[13] ^ load64(input_cursor + 104);
lanes13:
    input_state[12] = output_state[12] ^ load64(input_cursor + 96);
lanes12:
    input_state[11] = output_state[11] ^ load64(input_cursor + 88);
lanes11:
    input_state[10] = output_state[10] ^ load64(input_cursor + 80);
lanes10:
    input_state[9] = output_state[9] ^ load64(input_cursor + 72);
lanes9:
    input_state[8] = output_state[8] ^ load64(input_cursor + 64);
lanes8:
    input_state[7] = output_state[7] ^ load64(input_cursor + 56);
lanes7:
    input_state[6] = output_state[6] ^ load64(input_cursor + 48);
lanes6:
    input_state[5] = output_state[5] ^ load64(input_cursor + 40);
lanes5:
    input_state[4] = output_state[4] ^ load64(input_cursor + 32);
lanes4:
    input_state[3] = output_state[3] ^ load64(input_cursor + 24);
lanes3:
    input_state[2] = output_state[2] ^ load64(input_cursor + 16);
lanes2:
    input_state[1] = output_state[1] ^ load64(input_cursor + 8);
lanes1:
    input_state[0] = output_state[0] ^ load64(input_cursor);
lanes0:
    uint64_t padded_tail_lane = uint64_t{0x01} << (8 * partial_lane_bytes);
    if (partial_lane_bytes != 0) {
        padded_tail_lane |= load64(input_cursor + remaining_bytes - 8) >>
                            (8 * (8 - partial_lane_bytes));
    }
    input_state[full_tail_lanes] =
        output_state[full_tail_lanes] ^ padded_tail_lane;
    std::memcpy(
        input_state + full_tail_lanes + 1,
        output_state + full_tail_lanes + 1,
        (KECCAKF_LANES - 1 - full_tail_lanes) * 8);
    input_state[16] ^= uint64_t{0x80} << 56;
    output_state =
        keep_looking_up
            ? keccakf_memo_permute<false>(input_state, entry_count)
            : keccakf_memo_permute<false, false>(input_state, entry_count);
    std::memcpy(output, output_state, 32);

    // A hit or full table reuses this scratch; a miss advanced to a zero slot.
    if (input_state == keccakf_memo[entry_count].in) {
        std::memset(input_state, 0, KECCAKF_STATE_BYTES);
    }
    keccakf_memo_used = entry_count;
}

    #endif // MONAD_ZKVM_KECCAKF_MEMO

// Raw permutation for the sponge's non-memo path.
static inline void keccak_permute(uint64_t (*state)[25])
{
    zisk_keccakf(state);
}

// Select memoized or raw hashing at compile time.
template <bool Memo>
static void keccak256_sponge(
    void const *const input, size_t remaining_bytes, uint8_t output[32])
{
    constexpr size_t RATE_WORDS = KECCAK_RATE / 8; // 17

    #if MONAD_ZKVM_KECCAKF_MEMO
    if constexpr (Memo) {
        // Short inputs build their padded state directly input the memo.
        if (remaining_bytes < KECCAK_RATE) {
            keccak256_one_block(input, remaining_bytes, output);
        }
        else {
            keccak256_memo_sponge(input, remaining_bytes, output);
        }
        return;
    }
    #endif

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

extern "C"
{

void monad_zkvm_keccak256_fast(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_sponge<true>(in, len, out);
}

// Compute every permutation without caching; later calls may lose cache hits.
// Their hints still require valid indices and exact input-state matches.
void monad_zkvm_keccak256_fast_nomemo(
    void const *const in, size_t len, uint8_t out[32])
{
    keccak256_sponge<false>(in, len, out);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_KECCAK_TEST
