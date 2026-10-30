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

// Load eight bytes without requiring pointer alignment.
[[gnu::always_inline]] static inline uint64_t
load64(unsigned char const *const p)
{
    uint64_t v;
    __builtin_memcpy(&v, p, sizeof v);
    return v;
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
    sizeof(KeccakfEntry) == 512 &&
        sizeof(KeccakfEntry) > 2 * KECCAKF_STATE_BYTES,
    "an entry is the two states, padded to a shift");

        #if defined(MONAD_ZKVM_KECCAK_TEST) && !defined(MONAD_ZKVM_ZISK)
// Reach the full-table fallback in host tests.
constexpr size_t KECCAKF_MEMO_ENTRIES = 16;
        #else
constexpr size_t KECCAKF_MEMO_ENTRIES = size_t{1} << 18;
        #endif

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

// The index `state` was filed under, or KECCAKF_INDEX_NOT_FOUND.
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

// Finish a padded one-block input in the unpublished scratch entry.
// Accept hints only for published entries with an identical full input state.
// Scratch starts zeroed: misses advance to fresh entries; hits clear the
// leading WrittenLanes and padding lane 16; full-table calls clear all 25
// lanes.
template <size_t WrittenLanes>
[[gnu::always_inline]] static inline void keccak256_one_block_finish(
    KeccakfEntry &entry, uint64_t const used, uint8_t out[32])
{
    static_assert(WrittenLanes >= 1 && WrittenLanes <= 17);
    uint64_t *const state = entry.in;

    uint64_t const index = fcall_get_keccakf_index(state);
    if (index < used && keccakf_state_eq(keccakf_memo[index].in, state)) {
        std::memcpy(out, keccakf_memo[index].out, 32);
        std::memset(state, 0, WrittenLanes * sizeof(uint64_t));
        if constexpr (WrittenLanes < 17) {
            state[16] = 0;
        }
        return;
    }

    if (used == KECCAKF_MEMO_ENTRIES) {
        // Full table: permute the spare slot, then clear it for reuse.
        zisk_keccakf(&entry.in);
        std::memcpy(out, state, 32);
        std::memset(state, 0, KECCAKF_STATE_BYTES);
        return;
    }

    // Preserve `in`; copy only the rate to `out` for the permutation.
    // Both capacities are zero: this is the first block and `out` is unused.
    std::memcpy(entry.out, state, 17 * sizeof(uint64_t));
    fcall_set_keccakf_index(used);
    zisk_keccakf(&entry.out);
    // Publish only after both input and output are stored.
    keccakf_memo_used = used + 1;
    std::memcpy(out, entry.out, 32);
}

static void
keccak256_one_block(void const *const in, size_t const len, uint8_t out[32])
{
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");

    // Keep the count local across asm memory clobbers.
    uint64_t const used = keccakf_memo_used;
    KeccakfEntry &entry = keccakf_memo[used];
    uint64_t *const state = entry.in;

    if (len) {
        std::memcpy(state, in, len);
    }
    reinterpret_cast<unsigned char *>(state)[len] = 0x01;
    state[16] |= uint64_t{0x80} << 56;

    // Any of the 17 rate lanes may hold input or padding.
    keccak256_one_block_finish<17>(entry, used, out);
}

// Fixed lengths eliminate runtime dispatch and make copy/padding sizes
// constant. Scratch starts zeroed. The domain byte must precede lane 16,
// allowing a plain store of the final padding bit without overwriting input.
template <size_t InputBytes>
static void keccak256_one_block_fixed(void const *const in, uint8_t out[32])
{
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
    static_assert(
        InputBytes >= 1 && InputBytes + 1 <= 16 * 8,
        "lane 16 holds only the pad bit");

    uint64_t const used = keccakf_memo_used;
    KeccakfEntry &entry = keccakf_memo[used];
    uint64_t *const state = entry.in;

    std::memcpy(state, in, InputBytes);
    if constexpr (InputBytes % 8 == 0) {
        state[InputBytes / 8] = 0x01;
    }
    else {
        reinterpret_cast<unsigned char *>(state)[InputBytes] = 0x01;
    }
    state[16] = uint64_t{0x80} << 56;

    // The input and the 0x01 span the first (InputBytes + 1 + 7) / 8 lanes.
    keccak256_one_block_finish<(InputBytes + 1 + 7) / 8>(entry, used, out);
}

enum class Block
{
    First,
    Following
};
enum class Lookup
{
    Search,
    Skip
};
enum class Capacity
{
    Checked,
    Guaranteed
};

// Permute pre = keccakf_memo[used].in without changing it.
// A hit needs a valid index and an identical full input state.
// Hits return an earlier output; misses return pre + KECCAKF_LANES.
// Block::First copies only the rate into a fresh output: both capacities are
// zero. Other blocks and the reused spare need all 200 bytes. Lookup::Skip
// skips hints but still computes and caches the permutation.
// Capacity::Guaranteed skips capacity checks after the caller bounds all
// insertions. used is local to the caller, which writes it back after the
// digest.
template <
    Block block, Lookup lookup = Lookup::Search,
    Capacity capacity = Capacity::Checked>
static inline uint64_t const *
keccakf_memo_permute(uint64_t *const pre, uint64_t &used)
{
    if constexpr (lookup == Lookup::Search) {
        uint64_t const index = fcall_get_keccakf_index(pre);
        // Reject out-of-range hints before reading the table.
        if (index < used && keccakf_state_eq(keccakf_memo[index].in, pre)) {
            return keccakf_memo[index].out;
        }
    }
    uint64_t *const slot_out = pre + KECCAKF_LANES;
    auto *const post = reinterpret_cast<uint64_t(*)[KECCAKF_LANES]>(slot_out);
    if constexpr (capacity == Capacity::Checked) {
        if (used == KECCAKF_MEMO_ENTRIES) {
            // The reused spare may hold an earlier output; overwrite all lanes.
            keccakf_state_copy(slot_out, pre);
            zisk_keccakf(post);
            return slot_out;
        }
    }
    if constexpr (block == Block::First) {
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

// Build states in the memo, preserving the previous output's capacity.
// Scratch is zero on entry; later blocks overwrite all 25 lanes.
// Capacity::Guaranteed guarantees space for every permutation: len / 136 + 1 is
// at most (len >> 7) + 1. Hits consume no entries. Publish used on return.
template <Capacity capacity>
static void keccak256_memo_sponge(
    void const *const in, size_t len, uint8_t out[32], uint64_t used)
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17
    static_assert(
        KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
    auto const *p = static_cast<unsigned char const *>(in);

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
    uint64_t const *post =
        keccakf_memo_permute<Block::First, Lookup::Search, capacity>(pre, used);

    // Stop lookups after the first miss. This may forgo later hits, but
    // skipped lookups run the real permutation and cache it when space permits.
    bool look = post != pre + KECCAKF_LANES;

    // Full branch RLP: 3 header bytes + 16 * (1 prefix + 32 hash bytes)
    // + 1 empty-value byte = 532 bytes.
    // After a first-block miss, absorb its remaining 2 * 136 + 124 bytes
    // with fixed offsets and padding. Require three free memo slots;
    // otherwise use the general path below.
    constexpr size_t FULL_BRANCH_RLP_BYTES = 532;
    static_assert(
        FULL_BRANCH_RLP_BYTES - KECCAK_RATE == 2 * KECCAK_RATE + 15 * 8 + 4,
        "two middle blocks, then fifteen lanes and four bytes");
    if (MONAD_LIKELY(!look) && len == FULL_BRANCH_RLP_BYTES - KECCAK_RATE &&
        used + 3 <= KECCAKF_MEMO_ENTRIES) {
        // One opaque base for the three slots keeps every lane at a literal
        // offset from a single register.
        KeccakfEntry *entries = &keccakf_memo[used];
        asm("" : "+r"(entries));
        // Block 2: p follows block 1; post is its permutation result.
        // XOR the 136 input bytes into the state's first 17 lanes.
        for (size_t i = 0; i < WORDS; ++i) {
            entries[0].in[i] = post[i] ^ load64(p + 8 * i);
        }
        // Preserve the eight capacity lanes, which do not absorb input.
        std::memcpy(
            entries[0].in + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
        // Keep .in for future cache comparisons; permute its copy in .out.
        // Register each entry immediately before computing its permutation.
        keccakf_state_copy(entries[0].out, entries[0].in);
        fcall_set_keccakf_index(used);
        zisk_keccakf(&entries[0].out);

        // Block 3: repeat absorption using block 2's output state.
        unsigned char const *const third_block = p + KECCAK_RATE;
        for (size_t i = 0; i < WORDS; ++i) {
            entries[1].in[i] = entries[0].out[i] ^ load64(third_block + 8 * i);
        }
        std::memcpy(
            entries[1].in + WORDS,
            entries[0].out + WORDS,
            (KECCAKF_LANES - WORDS) * 8);
        keccakf_state_copy(entries[1].out, entries[1].in);
        fcall_set_keccakf_index(used + 1);
        zisk_keccakf(&entries[1].out);

        // Final block: 124 bytes = fifteen whole lanes + four bytes.
        unsigned char const *const final_block = p + 2 * KECCAK_RATE;
        for (size_t i = 0; i < 15; ++i) {
            entries[2].in[i] = entries[1].out[i] ^ load64(final_block + 8 * i);
        }
        // Read exactly four bytes to stay within the input. In byte order:
        // lane 15 = [last four bytes, 01, 00, 00, 00];
        // lane 16 = [00, 00, 00, 00, 00, 00, 00, 80].
        uint32_t last_bytes;
        __builtin_memcpy(&last_bytes, final_block + 15 * 8, sizeof last_bytes);
        entries[2].in[15] =
            entries[1].out[15] ^ (last_bytes | uint64_t{0x01} << 32);
        entries[2].in[16] = entries[1].out[16] ^ (uint64_t{0x80} << 56);
        std::memcpy(
            entries[2].in + WORDS,
            entries[1].out + WORDS,
            (KECCAKF_LANES - WORDS) * 8);
        keccakf_state_copy(entries[2].out, entries[2].in);
        fcall_set_keccakf_index(used + 2);
        zisk_keccakf(&entries[2].out);
        // Keccak-256 returns the first 32 bytes of the final state.
        std::memcpy(out, entries[2].out, 32);
        // Publish all three entries; the next scratch slot is still unwritten.
        keccakf_memo_used = used + 3;
        return;
    }

    while (look && len >= KECCAK_RATE) {
        pre = keccakf_memo[used].in;
        // Keep one opaque base pointer for the lanes to avoid extra saved
        // registers for their addresses.
        asm("" : "+r"(pre));
        for (size_t i = 0; i < WORDS; ++i) {
            pre[i] = post[i] ^ load64(p + 8 * i);
        }
        std::memcpy(pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
        post = keccakf_memo_permute<Block::Following, Lookup::Search, capacity>(
            pre, used);
        look = post != pre + KECCAKF_LANES;
        p += KECCAK_RATE;
        len -= KECCAK_RATE;
    }
    if constexpr (capacity == Capacity::Guaranteed) {
        // After a miss, each permutation inserts one entry. Walk the entry
        // array directly; if all lookups hit, pre remains the scratch slot.
        if (!look) {
            KeccakfEntry *next_entry = &keccakf_memo[used];
            while (len >= KECCAK_RATE) {
                pre = next_entry->in;
                asm("" : "+r"(pre));
                for (size_t i = 0; i < WORDS; ++i) {
                    pre[i] = post[i] ^ load64(p + 8 * i);
                }
                std::memcpy(
                    pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
                post = keccakf_memo_permute<
                    Block::Following,
                    Lookup::Skip,
                    Capacity::Guaranteed>(pre, used);
                ++next_entry;
                p += KECCAK_RATE;
                len -= KECCAK_RATE;
            }
            pre = next_entry->in;
        }
    }
    else {
        while (len >= KECCAK_RATE) {
            pre = keccakf_memo[used].in;
            asm("" : "+r"(pre));
            for (size_t i = 0; i < WORDS; ++i) {
                pre[i] = post[i] ^ load64(p + 8 * i);
            }
            std::memcpy(pre + WORDS, post + WORDS, (KECCAKF_LANES - WORDS) * 8);
            post =
                keccakf_memo_permute<Block::Following, Lookup::Skip>(pre, used);
            p += KECCAK_RATE;
            len -= KECCAK_RATE;
        }
        pre = keccakf_memo[used].in;
    }

    // Absorb the remaining bytes and Keccak padding (0x01 ... 0x80).
    // The partial lane is read backwards from the input end; the preceding
    // full block keeps the eight-byte load within the input.
    size_t const whole = len / 8;
    unsigned const rem = static_cast<unsigned>(len % 8);
    // Direct label addresses avoid switch-table offset arithmetic.
    // len < KECCAK_RATE guarantees whole is in [0, 16].
    static void *const entry[] = {
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
    if constexpr (capacity == Capacity::Guaranteed) {
        // A filing advances `used` past `pre` to a zero slot; only a hit
        // leaves the scratch in use, so only a hit clears it.
        if (look) {
            post = keccakf_memo_permute<
                Block::Following,
                Lookup::Search,
                Capacity::Guaranteed>(pre, used);
            if (post != pre + KECCAKF_LANES) {
                std::memcpy(out, post, 32);
                std::memset(pre, 0, KECCAKF_STATE_BYTES);
                keccakf_memo_used = used;
                return;
            }
        }
        else {
            post = keccakf_memo_permute<
                Block::Following,
                Lookup::Skip,
                Capacity::Guaranteed>(pre, used);
        }
        std::memcpy(out, post, 32);
    }
    else {
        post = look ? keccakf_memo_permute<Block::Following>(pre, used)
                    : keccakf_memo_permute<Block::Following, Lookup::Skip>(
                          pre, used);
        std::memcpy(out, post, 32);

        if (pre == keccakf_memo[used].in) {
            std::memset(pre, 0, KECCAKF_STATE_BYTES);
        }
    }
    keccakf_memo_used = used;
}

    #endif // MONAD_ZKVM_KECCAKF_MEMO

// Raw permutation for the sponge's non-memo path.
static inline void keccak_permute(uint64_t (*state)[25])
{
    zisk_keccakf(state);
}

// Templates require C++ linkage; keep this outside extern "C".
template <bool Memo>
static void keccak256_sponge(void const *const in, size_t len, uint8_t out[32])
{
    constexpr size_t WORDS = KECCAK_RATE / 8; // 17

    #if MONAD_ZKVM_KECCAKF_MEMO
    if constexpr (Memo) {
        // Short inputs build their padded state directly in the memo.
        if (len < KECCAK_RATE) {
            keccak256_one_block(in, len, out);
        }
        else {
            // Test the table's room once per digest rather than once per
            // permutation; see keccak256_memo_sponge for the bound.
            uint64_t const used = keccakf_memo_used;
            if (used + (len >> 7) < KECCAKF_MEMO_ENTRIES) {
                keccak256_memo_sponge<Capacity::Guaranteed>(in, len, out, used);
            }
            else {
                keccak256_memo_sponge<Capacity::Checked>(in, len, out, used);
            }
        }
        return;
    }
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

// Keep the same entry points when memoization is disabled.
template <size_t InputBytes>
[[gnu::always_inline]] static inline void
keccak256_fixed(void const *const in, uint8_t out[32])
{
    #if MONAD_ZKVM_KECCAKF_MEMO
    keccak256_one_block_fixed<InputBytes>(in, out);
    #else
    keccak256_sponge<true>(in, InputBytes, out);
    #endif
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

void monad_zkvm_keccak256_20(void const *const in, uint8_t out[32])
{
    keccak256_fixed<20>(in, out);
}

void monad_zkvm_keccak256_32(void const *const in, uint8_t out[32])
{
    keccak256_fixed<32>(in, out);
}

void monad_zkvm_keccak256_64(void const *const in, uint8_t out[32])
{
    keccak256_fixed<64>(in, out);
}

} // extern "C"

#endif // MONAD_ZKVM_ZISK || MONAD_ZKVM_KECCAK_TEST
