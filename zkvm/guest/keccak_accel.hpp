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

// Keccak-256 for the zkVM guest: absorb 136-byte blocks as 17 words, permute
// with a backend's Keccak-f, and apply Ethereum's 0x01/0x80 padding to the
// final block. keccak256_memo also reuses earlier permutations through a
// table the backend's executor indexes.

#pragma once

#include <category/core/config.hpp>

#include <cstddef>
#include <cstdint>
#include <cstring>

// Each backend's keccak.cpp defines the guest's two digests from the
// templates below: monad_keccak256 (category/crypto/keccak.h), which reuses
// Keccak-f results across digests, and this one, which makes no table lookups
// or inserts. Used for bytecode.
void monad_keccak256_nomemo(
    void const *input, size_t input_length, uint8_t output[32]);

MONAD_NAMESPACE_BEGIN

constexpr size_t KECCAK_RATE = 136;
constexpr size_t KECCAK_RATE_LANES = KECCAK_RATE / sizeof(uint64_t);
constexpr size_t KECCAKF_LANES = 25;
constexpr size_t KECCAKF_STATE_BYTES = KECCAKF_LANES * sizeof(uint64_t);
constexpr size_t KECCAK_CAPACITY_BYTES = KECCAKF_STATE_BYTES - KECCAK_RATE;

// Load eight bytes without requiring pointer alignment.
[[gnu::always_inline]] inline uint64_t
keccak_load64(unsigned char const *const bytes)
{
    uint64_t word;
    std::memcpy(&word, bytes, sizeof word);
    return word;
}

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

// A backend supplies the permutation and its executor's side of the memo:
//
//   static void keccakf(uint64_t state[25]);
//     Keccak-f[1600] on `state`, in place.
//   static uint64_t get_index(uint64_t const state[25]);
//     Ask the executor which table entry holds `state` as its input. The
//     result is an untrusted hint: KeccakMemo bounds the index and compares
//     all 25 lanes, so any out-of-range value reports a miss.
//   static void set_index(uint64_t index);
//     Tell the executor that the input of the next keccakf call is entry
//     `index`. No other permutation may run in between.

// What get_index returns from a backend that has no entry to suggest.
constexpr uint64_t KECCAKF_INDEX_NOT_FOUND = ~uint64_t{0};

// One table per backend. Entries below `used` are published: their input and
// output are final. The entry at `used` is scratch whose input is all zero
// between digests. The extra entry is that scratch once the table is full; it
// is never published, so a hint cannot select it.
template <class Backend>
struct KeccakfMemoTable
{
    static inline KeccakfEntry entries[KECCAKF_MEMO_ENTRIES + 1];
    static inline uint64_t used = 0;
};

// keccak256_sponge takes its states and its permutation from a policy:
//
//   uint64_t *first();
//     An all-zero state to build the first block in.
//   uint64_t *next(uint64_t const *previous);
//     A state to build the following block in. Its capacity lanes hold
//     those of `previous`, the last permutation's result.
//   uint64_t const *permute(uint64_t *state);
//     The permutation of `state`.
//   void finish(uint64_t const *state);
//     End the digest; `state` is the last one permuted.

// Permute one state in place.
template <class Backend>
struct KeccakNoMemo
{
    uint64_t state_[KECCAKF_LANES];

    [[gnu::always_inline]] uint64_t *first()
    {
        std::memset(state_, 0, KECCAKF_STATE_BYTES);
        return state_;
    }

    [[gnu::always_inline]] uint64_t *next(uint64_t const * /*previous*/)
    {
        return state_;
    }

    [[gnu::always_inline]] static uint64_t const *permute(uint64_t *const state)
    {
        Backend::keccakf(state);
        return state;
    }

    [[gnu::always_inline]] static uint64_t const *
    permute_first(uint64_t *const state)
    {
        return permute(state);
    }

    [[gnu::always_inline]] static void finish(uint64_t const * /*state*/) {}

    [[gnu::always_inline]] static void
    finish_only_block(uint64_t const * /*state*/)
    {
    }
};

// Build each state in the scratch entry's input and ask the executor for a
// published entry with the same input. The hint avoids a guest-side search
// over 200-byte states and is untrusted: it is accepted only when the index is
// published and all 25 lanes match. A hit returns that entry's output. A miss
// permutes a copy in the scratch entry's output and publishes the entry, so a
// stored output always comes from a real permutation in this execution.
template <class Backend>
struct KeccakMemo
{
    using Table = KeccakfMemoTable<Backend>;

    // Kept local so that backend calls do not force reloads of the global.
    uint64_t used_{Table::used};
    // Lookups stop at a digest's first miss: the states after it depend on a
    // state the table had not seen, so they are unlikely to be in it either.
    bool lookup_{true};

    [[gnu::always_inline]] uint64_t *first() const
    {
        return Table::entries[used_].in;
    }

    [[gnu::always_inline]] uint64_t *next(uint64_t const *const previous) const
    {
        uint64_t *const state = Table::entries[used_].in;
        std::memcpy(
            state + KECCAK_RATE_LANES,
            previous + KECCAK_RATE_LANES,
            KECCAK_CAPACITY_BYTES);
        return state;
    }

    [[gnu::always_inline]] uint64_t const *permute(uint64_t *const state)
    {
        return this->template permute_block<false>(state);
    }

    // The first block's capacity lanes are zero, and so are those of a
    // scratch output that no permutation has written.
    [[gnu::always_inline]] uint64_t const *permute_first(uint64_t *const state)
    {
        return this->template permute_block<true>(state);
    }

    template <bool FirstBlock>
    [[gnu::always_inline]] uint64_t const *permute_block(uint64_t *const state)
    {
        if (lookup_) {
            uint64_t const index = Backend::get_index(state);
            // Reject out-of-range hints before reading the table.
            if (index < used_ &&
                std::memcmp(
                    Table::entries[index].in, state, KECCAKF_STATE_BYTES) ==
                    0) {
                return Table::entries[index].out;
            }
            lookup_ = false;
        }
        uint64_t *const output = Table::entries[used_].out;
        if (used_ == KECCAKF_MEMO_ENTRIES) {
            // Full table: compute in the spare entry without publishing it.
            // Its output may hold an earlier result, so copy every lane.
            std::memcpy(output, state, KECCAKF_STATE_BYTES);
            Backend::keccakf(output);
            return output;
        }
        std::memcpy(
            output, state, FirstBlock ? KECCAK_RATE : KECCAKF_STATE_BYTES);
        // Tie this entry to the next permutation; keep the calls adjacent.
        Backend::set_index(used_);
        Backend::keccakf(output);
        // Publish only after both input and output are stored.
        ++used_;
        return output;
    }

    [[gnu::always_inline]] void finish(uint64_t const *const state) const
    {
        // A hit or a full table leaves the last state in the scratch entry.
        uint64_t *const scratch = Table::entries[used_].in;
        if (state == scratch) {
            std::memset(scratch, 0, KECCAKF_STATE_BYTES);
        }
        Table::used = used_;
    }

    // As finish, for a digest whose only block is `state`.
    [[gnu::always_inline]] void
    finish_only_block(uint64_t const *const state) const
    {
        uint64_t *const scratch = Table::entries[used_].in;
        if (state == scratch) {
            // A hit ran no permutation here: only the rate is non-zero. A
            // full table permuted the output, not this input.
            std::memset(scratch, 0, KECCAK_RATE);
        }
        Table::used = used_;
    }
};

// XOR one 136-byte block into the rate lanes of `previous`, writing `state`.
[[gnu::always_inline]] inline void keccak_absorb(
    uint64_t *const state, uint64_t const *const previous,
    unsigned char const *const block)
{
    for (size_t i = 0; i < KECCAK_RATE_LANES; ++i) {
        state[i] = previous[i] ^ keccak_load64(block + 8 * i);
    }
}

// Absorb the final block: the `remaining_bytes` bytes at `input_cursor`,
// fewer than KECCAK_RATE, then the padding, XORed into the rate lanes of
// `previous` and written to `state`. `state` is `previous` itself, or a state
// whose capacity lanes already hold those of `previous`. GCC unrolls the loop
// over the complete lanes into a chain that exits after the last one. The
// partial lane is read backwards from the end of the input, so the eight
// bytes before that end must be readable; a preceding block keeps them in
// bounds.
[[gnu::always_inline]] inline void keccak_absorb_final(
    uint64_t *const state, uint64_t const *const previous,
    unsigned char const *const input_cursor, size_t const remaining_bytes)
{
    size_t const full_lanes = remaining_bytes / 8;
    unsigned const partial_bytes = static_cast<unsigned>(remaining_bytes % 8);
#pragma GCC unroll 16
    for (size_t i = 0; i < full_lanes; ++i) {
        state[i] = previous[i] ^ keccak_load64(input_cursor + 8 * i);
    }
    uint64_t padded_lane = uint64_t{0x01} << (8 * partial_bytes);
    if (partial_bytes != 0) {
        padded_lane |= keccak_load64(input_cursor + remaining_bytes - 8) >>
                       (8 * (8 - partial_bytes));
    }
    state[full_lanes] = previous[full_lanes] ^ padded_lane;
    if (state != previous) {
        std::memcpy(
            state + full_lanes + 1,
            previous + full_lanes + 1,
            (KECCAK_RATE_LANES - 1 - full_lanes) * 8);
    }
    state[16] ^= uint64_t{0x80} << 56;
}

// Absorb the final block of a full branch node's RLP: fifteen lanes and four
// bytes at `final_block`, then the padding, XORed into the rate lanes of
// `previous` and written to `state`, whose capacity lanes already hold those
// of `previous`.
[[gnu::always_inline]] inline void keccak_absorb_branch_final(
    uint64_t *const state, uint64_t const *const previous,
    unsigned char const *const final_block)
{
    for (size_t i = 0; i < 15; ++i) {
        state[i] = previous[i] ^ keccak_load64(final_block + 8 * i);
    }
    // Lane 15 is the last four bytes, then the 0x01 pad byte.
    uint32_t last_four_bytes;
    std::memcpy(&last_four_bytes, final_block + 15 * 8, sizeof last_four_bytes);
    state[15] = previous[15] ^ (last_four_bytes | uint64_t{0x01} << 32);
    state[16] = previous[16] ^ (uint64_t{0x80} << 56);
}

// Keccak-256: absorb 136-byte blocks, the last one padded with 0x01 ... 0x80,
// and return the first 32 bytes of the final state.
template <class Policy>
[[gnu::always_inline]] inline void keccak256_sponge(
    Policy policy, void const *const input, size_t remaining_bytes,
    uint8_t output[32])
{
    auto const *input_cursor = static_cast<unsigned char const *>(input);

    uint64_t *state = policy.first();

    if (remaining_bytes < KECCAK_RATE) {
        // The only block: pad it in place in the zeroed state.
        if (remaining_bytes != 0) {
            std::memcpy(state, input_cursor, remaining_bytes);
        }
        reinterpret_cast<unsigned char *>(state)[remaining_bytes] = 0x01;
        static_assert(
            KECCAK_RATE - 1 == 16 * 8 + 7, "the pad bit is byte 7 of lane 16");
        state[16] |= uint64_t{0x80} << 56;
        std::memcpy(output, policy.permute_first(state), 32);
        policy.finish_only_block(state);
        return;
    }
    {
        std::memcpy(state, input_cursor, KECCAK_RATE);
        uint64_t const *previous = policy.permute_first(state);
        input_cursor += KECCAK_RATE;
        remaining_bytes -= KECCAK_RATE;

        // A full branch node's RLP is 3 header bytes + 16 * (1 prefix +
        // 32 hash bytes) + 1 empty-value byte = 532 bytes, and it is the most
        // common long input. Absorb what follows its first block with fixed
        // offsets and padding.
        constexpr size_t FULL_BRANCH_RLP_BYTES = 532;
        static_assert(
            FULL_BRANCH_RLP_BYTES - KECCAK_RATE == 2 * KECCAK_RATE + 15 * 8 + 4,
            "two more full blocks, then fifteen lanes and four bytes");
        if (remaining_bytes == FULL_BRANCH_RLP_BYTES - KECCAK_RATE) [[likely]] {
            state = policy.next(previous);
            keccak_absorb(state, previous, input_cursor);
            previous = policy.permute(state);

            state = policy.next(previous);
            keccak_absorb(state, previous, input_cursor + KECCAK_RATE);
            previous = policy.permute(state);

            state = policy.next(previous);
            keccak_absorb_branch_final(
                state, previous, input_cursor + 2 * KECCAK_RATE);

            std::memcpy(output, policy.permute(state), 32);
            policy.finish(state);
            return;
        }

        while (remaining_bytes >= KECCAK_RATE) {
            state = policy.next(previous);
            keccak_absorb(state, previous, input_cursor);
            previous = policy.permute(state);
            input_cursor += KECCAK_RATE;
            remaining_bytes -= KECCAK_RATE;
        }

        // Final block: the remaining bytes, then the padding.
        state = policy.next(previous);
        keccak_absorb_final(state, previous, input_cursor, remaining_bytes);
    }

    std::memcpy(output, policy.permute(state), 32);
    policy.finish(state);
}

// Keccak-256 that reuses Keccak-f results across digests.
template <class Backend>
[[gnu::always_inline]] inline void keccak256_memo(
    void const *const input, size_t const input_length, uint8_t output[32])
{
    keccak256_sponge(KeccakMemo<Backend>{}, input, input_length, output);
}

// Same digest without table lookups or inserts.
template <class Backend>
[[gnu::always_inline]] inline void keccak256_nomemo(
    void const *const input, size_t const input_length, uint8_t output[32])
{
    keccak256_sponge(KeccakNoMemo<Backend>{}, input, input_length, output);
}

MONAD_NAMESPACE_END
