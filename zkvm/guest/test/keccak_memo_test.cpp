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
    std::array<State, KECCAKF_MEMO_ENTRIES> recorded{};
    size_t recorded_count = 0;
    size_t lookups = 0; // Hint requests since the last reset.
    size_t checks = 0; // Digest comparisons across all scenarios.
    Hint hint = Hint::Find;

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
        recorded_count = 0;
        lookups = 0;
        hint = Hint::Find;
    }

    void check(void const *const input, size_t const len)
    {
        // Compare the complete digest with ethash, independently of whether
        // the memo accepted, rejected or skipped a hint.
        std::array<uint8_t, 32> actual{};
        monad_zkvm_keccak256_fast(input, len, actual.data());
        auto const expected =
            ethash_keccak256(static_cast<uint8_t const *>(input), len);
        if (std::memcmp(actual.data(), expected.bytes, actual.size()) != 0) {
            std::fprintf(
                stderr,
                "Keccak digest differs from ethash: length=%zu, "
                "hint_mode=%u\n",
                len,
                static_cast<unsigned>(hint));
            std::exit(1);
        }
        ++checks;
        // A completed digest must have published every registered entry.
        require(keccakf_memo_used == recorded_count, "publication count");
        State const zero{};
        // The next input slot (or the spare when full) must be ready for a
        // short digest, which does not overwrite all 200 bytes.
        require(
            std::memcmp(
                keccakf_memo[keccakf_memo_used].in,
                zero.data(),
                KECCAKF_STATE_BYTES) == 0,
            "scratch input not cleared");
        for (size_t i = 0; i < recorded_count; ++i) {
            // Check both halves of every cached entry: its input is immutable
            // and its full output equals a fresh software permutation.
            require(
                std::memcmp(
                    keccakf_memo[i].in,
                    recorded[i].data(),
                    KECCAKF_STATE_BYTES) == 0,
                "published input changed");
            uint64_t expected_state[KECCAKF_LANES];
            std::memcpy(
                expected_state, recorded[i].data(), sizeof(expected_state));
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
    require(index == recorded_count, "insertion index is not append-only");
    require(index < recorded.size(), "published the spare slot");
    std::memcpy(
        recorded[index].data(), keccakf_memo[index].in, KECCAKF_STATE_BYTES);
    ++recorded_count;
}

uint64_t test_get_keccakf_index(uint64_t const *const state)
{
    // Deliberately return bad hints in the adversarial modes. Rejection must
    // happen in the production memo code, not in this simulated executor.
    ++lookups;
    switch (hint) {
    case Hint::Missing:
        return KECCAKF_INDEX_NOT_FOUND;
    case Hint::OutOfRange:
        return KECCAKF_MEMO_ENTRIES + 1;
    case Hint::Unpublished:
        // The scratch input matches, but its output is not a cached result.
        return recorded_count;
    case Hint::Mismatch:
        return 0;
    case Hint::Find:
        for (size_t i = 0; i < recorded_count; ++i) {
            if (std::memcmp(recorded[i].data(), state, KECCAKF_STATE_BYTES) ==
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
    require(recorded_count == 1, "empty-input hit inserted another entry");

    // Every remainder, input alignment and pattern: misses followed by hits.
    constexpr size_t max_len = 4 * KECCAK_RATE;
    // The extra seven bytes allow offsets 0..7 without shortening the input.
    alignas(8) std::array<uint8_t, max_len + 7> buffer{};
    for (unsigned pattern = 0; pattern < 3; ++pattern) {
        // All-zero, all-one and deterministic pseudo-random byte patterns.
        for (size_t alignment = 0; alignment < 8; ++alignment) {
            auto *const input = buffer.data() + alignment;
            uint32_t random = 0x12345678;
            for (size_t i = 0; i < max_len; ++i) {
                random = random * 1664525u + 1013904223u;
                input[i] = pattern == 0   ? uint8_t{0}
                           : pattern == 1 ? uint8_t{0xff}
                                          : static_cast<uint8_t>(random >> 24);
            }
            for (size_t len = 0; len <= max_len; ++len) {
                reset();
                check(input, len);
                size_t const entries = recorded_count;
                // Padding always adds a block, even at an exact rate multiple.
                require(
                    entries == len / KECCAK_RATE + 1,
                    "miss did not populate memo");
                require(lookups == 1, "lookup continued after the first miss");
                // Replay without resetting: every state should now be cached.
                check(input, len);
                require(
                    recorded_count == entries,
                    "repeated digest missed the cache");
                // One request on the first digest, then one per cached state.
                require(
                    lookups == entries + 1, "repeated digest skipped a lookup");
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
    constexpr std::array<size_t, 11> lengths{
        0, 1, 135, 136, 137, 271, 272, 532, 1087, 1088, 1089};
    for (auto const mode :
         {Hint::Find,
          Hint::Missing,
          Hint::OutOfRange,
          Hint::Unpublished,
          Hint::Mismatch}) {
        for (size_t alignment = 0; alignment < 8; ++alignment) {
            for (size_t const len : lengths) {
                reset();
                uint8_t const seed = 0x42;
                // Make index 0 valid, so Mismatch tests state equality rather
                // than just the index bound.
                check(&seed, 1);
                hint = mode;
                check(longer.data() + alignment, len);
                check(longer.data() + alignment, len);
                check(nullptr, 0);
            }
        }
    }

    // A valid index with an equal rate but different capacity must be rejected.
    reset();
    alignas(8) std::array<uint8_t, 2 * KECCAK_RATE> collision{};
    check(collision.data(), KECCAK_RATE);
    // Choose block 2 so absorption gives post XOR (post XOR old_input),
    // reproducing entry 0's 136-byte rate. Its 64-byte capacity instead comes
    // from post and differs: comparing only the rate would accept a false hit.
    for (size_t i = 0; i < KECCAK_RATE / 8; ++i) {
        uint64_t const word = keccakf_memo[0].out[i] ^ keccakf_memo[0].in[i];
        std::memcpy(
            collision.data() + KECCAK_RATE + i * 8, &word, sizeof(word));
    }
    State const zero{};
    require(
        std::memcmp(keccakf_memo[0].out + 17, zero.data(), 64) != 0,
        "capacity-collision fixture has a zero capacity");
    hint = Hint::Mismatch;
    check(collision.data(), collision.size());
    // The first digest cached two states. The second reuses its first state,
    // then adds the capacity mismatch and the final padded state.
    require(recorded_count == 4, "accepted a capacity-only mismatch");
    // One initial miss, then a hit and a miss; the final lookup is skipped.
    require(lookups == 3, "expected a hit, then a miss, then no lookup");

    // Cross the one-time capacity check with zero through five free
    // entries. Both lengths need four permutations, including padding.
    for (size_t free_entries = 0; free_entries <= 5; ++free_entries) {
        for (size_t len : {408u, 532u}) {
            reset();
            for (uint8_t i = 0; i < KECCAKF_MEMO_ENTRIES - free_entries; ++i) {
                check(&i, 1);
            }
            check(longer.data(), len);
            require(
                recorded_count == KECCAKF_MEMO_ENTRIES - free_entries +
                                      (free_entries < 4 ? free_entries : 4),
                "unexpected insertion count at capacity boundary");
            check(longer.data(), len);
            check(nullptr, 0);
        }
    }

    // Leave one free entry: the next digest fills it on its first block and
    // must use the spare for the rest, without modifying published entries.
    reset();
    for (uint8_t i = 0; i < KECCAKF_MEMO_ENTRIES - 1; ++i) {
        check(&i, 1);
    }
    check(longer.data(), longer.size() - 7);
    require(recorded_count == KECCAKF_MEMO_ENTRIES, "table did not fill");
    for (auto const mode :
         {Hint::Find,
          Hint::Missing,
          Hint::OutOfRange,
          Hint::Unpublished,
          Hint::Mismatch}) {
        hint = mode;
        for (size_t const len : lengths) {
            check(longer.data() + 1, len);
            check(longer.data() + 1, len);
            // Reuse scratch after a full-table permutation.
            check(nullptr, 0);
        }
        uint8_t const cached = 3;
        hint = Hint::Find;
        check(&cached, 1); // Published entries remain usable when full.
    }

    // The bytecode entry point must neither query nor populate the memo.
    for (bool const full : {true, false}) {
        if (!full) {
            reset();
        }
        size_t const queries = lookups;
        size_t const entries = recorded_count;
        for (size_t const len : lengths) {
            std::array<uint8_t, 32> actual{};
            monad_zkvm_keccak256_fast_nomemo(
                longer.data() + 1, len, actual.data());
            auto const expected = ethash_keccak256(longer.data() + 1, len);
            require(
                std::memcmp(actual.data(), expected.bytes, actual.size()) == 0,
                "non-memo digest mismatch");
            ++checks;
        }
        require(
            lookups == queries && recorded_count == entries,
            "bytecode path touched the memo");
    }
    std::printf("Keccak memo: %zu reference comparisons passed\n", checks);
}
