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

// Include the production implementation to reset and inspect its private memo.
// Only the executor hints and permutation are replaced by host implementations.
// NOLINTNEXTLINE(bugprone-suspicious-include)
#include "../keccak_accel.cpp"

#include <ethash/keccak.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

namespace
{
    enum class Hint
    {
        // Simulate honest lookups and dishonest hints to test guest-side
        // validation.
        Find, // Search for an identical state, as an honest executor would.
        Missing, // Report no cached result, even if one exists.
        OutOfRange, // Return an index beyond the table's allocation.
        Unpublished, // Return the scratch index, which is not a published
                     // entry.
        Mismatch // Return entry 0 regardless of the requested state.
    };

    using State = std::array<uint64_t, KECCAKF_LANES>;
    // The simulated executor keeps its own input snapshots. The guest must
    // validate its hints against the real memo, whose outputs we check below.
    std::array<State, KECCAKF_MEMO_ENTRIES> recorded_inputs{};
    size_t recorded_entry_count = 0;
    size_t hint_lookup_count = 0; // Hint requests since the last reset.
    size_t comparison_count = 0; // Digest comparisons across all scenarios.
    Hint hint_mode = Hint::Find;

    void require(bool const ok, char const *const message)
    {
        // Keep checks active in release builds, unlike assert().
        if (!ok) {
            std::fprintf(stderr, "Keccak memo: %s\n", message);
            std::exit(1);
        }
    }

    void reset()
    {
        // Start with an empty guest memo and executor registry. Keep only the
        // total comparison count; each scenario chooses its own hint behavior.
        std::memset(keccakf_memo, 0, sizeof(keccakf_memo));
        keccakf_memo_used = 0;
        recorded_entry_count = 0;
        hint_lookup_count = 0;
        hint_mode = Hint::Find;
    }

    void check(void const *const input, size_t const input_length)
    {
        // Compare the complete digest with ethash, independently of whether
        // the memo accepted, rejected or skipped a hint.
        std::array<uint8_t, 32> actual{};
        monad_zkvm_keccak256_fast(input, input_length, actual.data());
        auto const expected =
            ethash_keccak256(static_cast<uint8_t const *>(input), input_length);
        if (std::memcmp(actual.data(), expected.bytes, actual.size()) != 0) {
            std::fprintf(
                stderr,
                "Keccak digest differs from ethash: length=%zu, "
                "hint_mode=%u\n",
                input_length,
                static_cast<unsigned>(hint_mode));
            std::exit(1);
        }
        ++comparison_count;
        // A completed digest must have published every registered entry.
        require(keccakf_memo_used == recorded_entry_count, "publication count");
        State const zero{};
        // The next input slot (or the spare when full) must be ready for a
        // short digest, which does not overwrite all 200 bytes.
        require(
            std::memcmp(
                keccakf_memo[keccakf_memo_used].in,
                zero.data(),
                KECCAKF_STATE_BYTES) == 0,
            "scratch input not cleared");
        for (size_t i = 0; i < recorded_entry_count; ++i) {
            // Check both halves of every cached entry: its input is immutable
            // and its full output equals a fresh software permutation.
            require(
                std::memcmp(
                    keccakf_memo[i].in,
                    recorded_inputs[i].data(),
                    KECCAKF_STATE_BYTES) == 0,
                "published input changed");
            uint64_t expected_state[KECCAKF_LANES];
            std::memcpy(
                expected_state,
                recorded_inputs[i].data(),
                sizeof(expected_state));
            test_keccak_f(&expected_state);
            require(
                std::memcmp(
                    keccakf_memo[i].out,
                    expected_state,
                    sizeof(expected_state)) == 0,
                "published output is not the permutation of its input");
        }
    }
}

void test_set_keccakf_index(uint64_t const index)
{
    // The guest registers this index immediately before the real permutation.
    // Remember its input now; check() verifies the completed output afterward.
    require(
        index == recorded_entry_count, "insertion index is not append-only");
    require(index < recorded_inputs.size(), "published the spare slot");
    std::memcpy(
        recorded_inputs[index].data(),
        keccakf_memo[index].in,
        KECCAKF_STATE_BYTES);
    ++recorded_entry_count;
}

uint64_t test_get_keccakf_index(uint64_t const *const state)
{
    // Deliberately return bad hints in the adversarial modes. Rejection must
    // happen in the production memo code, not in this simulated executor.
    ++hint_lookup_count;
    switch (hint_mode) {
    case Hint::Missing:
        return KECCAKF_INDEX_NOT_FOUND;
    case Hint::OutOfRange:
        return KECCAKF_MEMO_ENTRIES + 1;
    case Hint::Unpublished:
        // The scratch input matches, but its output is not a cached result.
        return recorded_entry_count;
    case Hint::Mismatch:
        return 0;
    case Hint::Find:
        for (size_t i = 0; i < recorded_entry_count; ++i) {
            if (std::memcmp(
                    recorded_inputs[i].data(), state, KECCAKF_STATE_BYTES) ==
                0) {
                return i;
            }
        }
        return KECCAKF_INDEX_NOT_FOUND;
    }
    std::abort();
}

int main()
{
    reset();
    check(nullptr, 0);
    check(nullptr, 0);
    require(
        recorded_entry_count == 1, "empty-input hit inserted another entry");

    // Every remainder, input alignment and pattern: misses followed by hits.
    constexpr size_t max_input_length = 4 * KECCAK_RATE;
    // The extra seven bytes allow offsets 0..7 without shortening the input.
    alignas(8) std::array<uint8_t, max_input_length + 7> buffer{};
    for (unsigned pattern = 0; pattern < 3; ++pattern) {
        // All-zero, all-one and deterministic pseudo-random byte patterns.
        for (size_t alignment_offset = 0; alignment_offset < 8;
             ++alignment_offset) {
            auto *const input = buffer.data() + alignment_offset;
            uint32_t random_state = 0x12345678;
            for (size_t i = 0; i < max_input_length; ++i) {
                random_state = random_state * 1664525u + 1013904223u;
                input[i] = pattern == 0 ? uint8_t{0}
                           : pattern == 1
                               ? uint8_t{0xff}
                               : static_cast<uint8_t>(random_state >> 24);
            }
            for (size_t input_length = 0; input_length <= max_input_length;
                 ++input_length) {
                reset();
                check(input, input_length);
                size_t const entries = recorded_entry_count;
                // Padding always adds a block, even at an exact rate multiple.
                require(
                    entries == input_length / KECCAK_RATE + 1,
                    "miss did not populate memo");
                require(
                    hint_lookup_count == 1,
                    "lookup continued after the first miss");
                // Replay without resetting: every state should now be cached.
                check(input, input_length);
                require(
                    recorded_entry_count == entries,
                    "repeated digest missed the cache");
                // One request on the first digest, then one per cached state.
                require(
                    hint_lookup_count == entries + 1,
                    "repeated digest skipped a lookup");
                check(nullptr, 0); // Reuse scratch after a hit.
            }
        }
    }

    // Exercise both sides of the aligned-copy threshold, with invalid hints.
    alignas(8) std::array<uint8_t, 9 * KECCAK_RATE + 7> longer{};
    for (size_t i = 0; i < longer.size(); ++i) {
        longer[i] = static_cast<uint8_t>(i * 37 + 11);
    }
    // Rate boundaries (136 bytes) and the aligned-copy limit (1088 bytes).
    constexpr std::array<size_t, 10> lengths{
        0, 1, 135, 136, 137, 271, 272, 1087, 1088, 1089};
    for (auto const mode :
         {Hint::Find,
          Hint::Missing,
          Hint::OutOfRange,
          Hint::Unpublished,
          Hint::Mismatch}) {
        for (size_t alignment_offset = 0; alignment_offset < 8;
             ++alignment_offset) {
            for (size_t const input_length : lengths) {
                reset();
                uint8_t const seed = 0x42;
                // Make index 0 valid, so Mismatch tests state equality rather
                // than just the index bound.
                check(&seed, 1);
                hint_mode = mode;
                check(longer.data() + alignment_offset, input_length);
                check(longer.data() + alignment_offset, input_length);
                check(nullptr, 0);
            }
        }
    }

    // A valid index with an equal rate but different capacity must be rejected.
    reset();
    alignas(8) std::array<uint8_t, 2 * KECCAK_RATE> capacity_mismatch_input{};
    check(capacity_mismatch_input.data(), KECCAK_RATE);
    // Choose block 2 so absorption gives post XOR (post XOR old_input),
    // reproducing entry 0's 136-byte rate. Its 64-byte capacity instead comes
    // from post and differs: comparing only the rate would accept a false hit.
    for (size_t i = 0; i < KECCAK_RATE / 8; ++i) {
        uint64_t const word = keccakf_memo[0].out[i] ^ keccakf_memo[0].in[i];
        std::memcpy(
            capacity_mismatch_input.data() + KECCAK_RATE + i * 8,
            &word,
            sizeof(word));
    }
    State const zero{};
    require(
        std::memcmp(keccakf_memo[0].out + 17, zero.data(), 64) != 0,
        "capacity-collision fixture has a zero capacity");
    hint_mode = Hint::Mismatch;
    check(capacity_mismatch_input.data(), capacity_mismatch_input.size());
    // The first digest cached two states. The second reuses its first state,
    // then adds the capacity mismatch and the final padded state.
    require(recorded_entry_count == 4, "accepted a capacity-only mismatch");
    // One initial miss, then a hit and a miss; the final lookup is skipped.
    require(
        hint_lookup_count == 3, "expected a hit, then a miss, then no lookup");

    // Leave one free entry: the next digest fills it on its first block and
    // must use the spare for the rest, without modifying published entries.
    reset();
    for (uint8_t i = 0; i < KECCAKF_MEMO_ENTRIES - 1; ++i) {
        check(&i, 1);
    }
    check(longer.data(), longer.size() - 7);
    require(recorded_entry_count == KECCAKF_MEMO_ENTRIES, "table did not fill");
    for (auto const mode :
         {Hint::Find,
          Hint::Missing,
          Hint::OutOfRange,
          Hint::Unpublished,
          Hint::Mismatch}) {
        hint_mode = mode;
        for (size_t const input_length : lengths) {
            check(longer.data() + 1, input_length);
            check(longer.data() + 1, input_length);
            // Reuse scratch after a full-table permutation.
            check(nullptr, 0);
        }
        uint8_t const cached = 3;
        hint_mode = Hint::Find;
        check(&cached, 1); // Published entries remain usable when full.
    }

    // The bytecode entry point must neither query nor populate the memo.
    for (bool const table_full : {true, false}) {
        if (!table_full) {
            reset();
        }
        size_t const initial_lookup_count = hint_lookup_count;
        size_t const entries = recorded_entry_count;
        for (size_t const input_length : lengths) {
            std::array<uint8_t, 32> actual{};
            monad_zkvm_keccak256_fast_nomemo(
                longer.data() + 1, input_length, actual.data());
            auto const expected =
                ethash_keccak256(longer.data() + 1, input_length);
            require(
                std::memcmp(actual.data(), expected.bytes, actual.size()) == 0,
                "non-memo digest mismatch");
            ++comparison_count;
        }
        require(
            hint_lookup_count == initial_lookup_count &&
                recorded_entry_count == entries,
            "bytecode path touched the memo");
    }
    std::printf(
        "Keccak memo: %zu reference comparisons passed\n", comparison_count);
}
