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

// zkvm/guest/keccak_accel.hpp under two backends: the x86 runner's, which
// has no executor, through the runner's entry points; and one that plays the
// executor, with honest lookups and dishonest hints.

#include <category/crypto/keccak.h>
#include <zkvm/guest/keccak_accel.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <format>
#include <initializer_list>
#include <map>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <sys/mman.h>
#include <unistd.h>

// aws-lc's Keccak-f[1600] and its Keccak-256 with Ethereum's padding
// (<openssl/digest.h>). The root CMakeLists.txt prefixes aws-lc's symbols
// with AWS_.
extern "C" void AWS_KeccakF1600(uint64_t state[5][5]);
struct env_md_st;
struct engine_st;
extern "C" env_md_st const *AWS_EVP_keccak256();
extern "C" int AWS_EVP_Digest(
    void const *data, size_t length, uint8_t *digest, unsigned *digest_length,
    env_md_st const *type, engine_st *engine);

namespace
{
    using namespace monad;

    // The expected digest, from a sponge that shares no code with
    // zkvm/guest/keccak_accel.hpp. The test binary's monad_keccak256 is the
    // code under test.
    std::array<uint8_t, 32>
    reference_keccak256(void const *const input, size_t const input_length)
    {
        std::array<uint8_t, 32> digest{};
        int const ok = AWS_EVP_Digest(
            input,
            input_length,
            digest.data(),
            nullptr,
            AWS_EVP_keccak256(),
            nullptr);
        if (ok != 1) {
            throw std::runtime_error{"aws-lc Keccak-256 failed"};
        }
        return digest;
    }

    void software_keccakf(uint64_t state[25])
    {
        AWS_KeccakF1600(reinterpret_cast<uint64_t(*)[5]>(state));
    }

    // The backend under test. Its lookups follow hint_mode, and its inserts
    // record what the memo files.
    struct Executor
    {
        static void keccakf(uint64_t state[25]);
        static uint64_t get_index(uint64_t const *state);
        static void set_index(uint64_t index);
    };

    auto &keccakf_memo = KeccakfMemoTable<Executor>::entries;
    uint64_t &keccakf_memo_used = KeccakfMemoTable<Executor>::used;

    enum class Hint
    {
        // Simulate honest lookups and dishonest hints to test guest-side
        // validation.
        Find, // Search for an identical state, as an honest executor would.
        Missing, // Report no cached result, even if one exists.
        OutOfRange, // Return an index beyond the table's allocation.
        Unpublished, // Return the scratch index, which is not a published
                     // entry.
        Mismatch // Return mismatch_index regardless of the requested state.
    };

    using State = std::array<uint64_t, KECCAKF_LANES>;
    // The simulated executor keeps its own input snapshots. The guest must
    // validate its hints against the real memo, whose outputs we check below.
    std::vector<State> recorded_inputs(KECCAKF_MEMO_ENTRIES);
    // First index recorded for each input, as an honest executor reports it.
    std::map<State, uint64_t> index_of_input;
    size_t recorded_entry_count = 0;
    // Entries below this were compared with a software permutation.
    size_t verified_entry_count = 0;
    size_t hint_lookup_count = 0; // Hint requests since the last reset.
    Hint hint_mode = Hint::Find;
    // Lookups still to answer as Hint::Find before hint_mode applies.
    size_t honest_lookup_count = 0;
    uint64_t mismatch_index = 0;
    size_t permutation_count = 0; // Backend permutations since the last reset.
    // The index set_index filed, until the permutation it announces runs.
    std::optional<uint64_t> filed_index;

    // Fail the running test from any depth, including the backend's functions.
    void require(bool const ok, std::string_view const message)
    {
        if (!ok) {
            throw std::logic_error{std::string{message}};
        }
    }

    // Drop every entry from `count` up, leaving the memo and the executor as
    // they were when only `count` entries had been published. The table is
    // too large to refill for each scenario.
    void truncate(size_t const count)
    {
        require(count <= recorded_entry_count, "truncating past the end");
        // The scratch entry sits at keccakf_memo_used; clear it as well.
        std::memset(
            &keccakf_memo[count],
            0,
            (keccakf_memo_used - count + 1) * sizeof(KeccakfEntry));
        for (size_t i = count; i < recorded_entry_count; ++i) {
            auto const it = index_of_input.find(recorded_inputs[i]);
            if (it != index_of_input.end() && it->second >= count) {
                index_of_input.erase(it);
            }
        }
        keccakf_memo_used = count;
        recorded_entry_count = count;
        if (verified_entry_count > count) {
            verified_entry_count = count;
        }
        hint_lookup_count = 0;
        hint_mode = Hint::Find;
        honest_lookup_count = 0;
        mismatch_index = 0;
        permutation_count = 0;
        filed_index.reset();
    }

    // Start with an empty guest memo and executor registry; each scenario
    // chooses its own hint behavior.
    void reset()
    {
        truncate(0);
    }

    // Check both halves of the cached entries from `first` up: the input is
    // immutable and the full output equals a fresh software permutation.
    void verify_entries(size_t const first)
    {
        for (size_t i = first; i < recorded_entry_count; ++i) {
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
            software_keccakf(expected_state);
            require(
                std::memcmp(
                    keccakf_memo[i].out,
                    expected_state,
                    sizeof(expected_state)) == 0,
                "published output is not the permutation of its input");
        }
        verified_entry_count = recorded_entry_count;
    }

    void check(void const *const input, size_t const input_length)
    {
        // Compare the complete digest with the reference, independently of
        // whether the memo accepted, rejected or skipped a hint.
        std::array<uint8_t, 32> actual{};
        size_t const entries = recorded_entry_count;
        size_t const permutations = permutation_count;
        keccak256_memo<Executor>(input, input_length, actual.data());
        auto const expected = reference_keccak256(input, input_length);
        require(
            actual == expected,
            std::format(
                "digest differs from the reference: length={}, hint_mode={}",
                input_length,
                static_cast<unsigned>(hint_mode)));
        // A completed digest must have published every registered entry.
        require(keccakf_memo_used == recorded_entry_count, "publication count");
        require(!filed_index, "filed an index without permuting its entry");
        // While the table has room, a permutation always publishes an entry,
        // so a hit runs none.
        require(
            recorded_entry_count - entries ==
                std::min(
                    permutation_count - permutations,
                    KECCAKF_MEMO_ENTRIES - entries),
            "permuted without publishing an entry");
        State const zero{};
        // The next input slot (or the spare when full) must be ready for a
        // short digest, which does not overwrite all 200 bytes.
        require(
            std::memcmp(
                keccakf_memo[keccakf_memo_used].in,
                zero.data(),
                KECCAKF_STATE_BYTES) == 0,
            "scratch input not cleared");
        // Verify the entries this digest published, and re-verify the few
        // before them, where a stray write would most likely land.
        // verify_entries(0) covers the whole table after the large scenarios.
        constexpr size_t recheck = 8;
        verify_entries(
            verified_entry_count > recheck ? verified_entry_count - recheck
                                           : 0);
    }

    // Publish distinct four-byte inputs until `count` entries exist. Entry i
    // of a table filled from empty holds the input i.
    void fill_to(size_t const count)
    {
        while (recorded_entry_count < count) {
            auto const input = static_cast<uint32_t>(recorded_entry_count);
            check(&input, sizeof(input));
            require(
                recorded_entry_count == size_t{input} + 1,
                "fill digest did not publish one entry");
        }
    }

    // Rate boundaries (136 bytes), a full branch node (532 bytes) and inputs
    // of eight blocks and more.
    constexpr std::array<size_t, 11> lengths{
        0, 1, 135, 136, 137, 271, 272, 532, 1087, 1088, 1089};

    // The extra seven bytes allow offsets 0..7 without shortening the input.
    alignas(8) std::array<uint8_t, 9 * KECCAK_RATE + 7> const longer = [] {
        std::array<uint8_t, 9 * KECCAK_RATE + 7> bytes{};
        for (size_t i = 0; i < bytes.size(); ++i) {
            bytes[i] = static_cast<uint8_t>(i * 37 + 11);
        }
        return bytes;
    }();

    constexpr size_t max_input_length = 4 * KECCAK_RATE;

    // All-zero, all-one or deterministic pseudo-random bytes.
    void fill_pattern(uint8_t *const input, unsigned const pattern)
    {
        uint32_t random_state = 0x12345678;
        for (size_t i = 0; i < max_input_length; ++i) {
            random_state = random_state * 1664525u + 1013904223u;
            input[i] = pattern == 0 ? uint8_t{0}
                       : pattern == 1
                           ? uint8_t{0xff}
                           : static_cast<uint8_t>(random_state >> 24);
        }
    }

    using Digest = std::array<uint8_t, 32>;
    using Keccak256 = void(void const *, size_t, uint8_t[32]);

    Digest digest_with(
        Keccak256 *const keccak256, uint8_t const *const input,
        size_t const input_length)
    {
        Digest digest{};
        keccak256(input, input_length, digest.data());
        return digest;
    }

    // The x86 runner's entry points, whose backend has no executor: every
    // lookup misses, so each digest computes its permutations.
    class KeccakEntryPoints : public ::testing::TestWithParam<Keccak256 *>
    {
    };
}

void Executor::keccakf(uint64_t state[25])
{
    ++permutation_count;
    if (filed_index) {
        // The executor caches the state this permutation reads, not the
        // entry, under the filed index.
        require(
            std::memcmp(
                state,
                recorded_inputs[*filed_index].data(),
                KECCAKF_STATE_BYTES) == 0,
            "permuted a state other than the filed entry's input");
        filed_index.reset();
    }
    software_keccakf(state);
}

void Executor::set_index(uint64_t const index)
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
    index_of_input.emplace(recorded_inputs[index], index);
    ++recorded_entry_count;
    require(!filed_index, "filed two indices for one permutation");
    filed_index = index;
}

uint64_t Executor::get_index(uint64_t const *const state)
{
    // Deliberately return bad hints in the adversarial modes. Rejection must
    // happen in the production memo code, not in this simulated executor.
    ++hint_lookup_count;
    Hint mode = hint_mode;
    if (honest_lookup_count > 0) {
        --honest_lookup_count;
        mode = Hint::Find;
    }
    switch (mode) {
    case Hint::Missing:
        return KECCAKF_INDEX_NOT_FOUND;
    case Hint::OutOfRange:
        return KECCAKF_MEMO_ENTRIES + 1;
    case Hint::Unpublished:
        // The scratch input matches, but its output is not a cached result.
        return recorded_entry_count;
    case Hint::Mismatch:
        return mismatch_index;
    case Hint::Find: {
        State key;
        std::memcpy(key.data(), state, KECCAKF_STATE_BYTES);
        auto const it = index_of_input.find(key);
        return it == index_of_input.end() ? KECCAKF_INDEX_NOT_FOUND
                                          : it->second;
    }
    }
    std::abort();
}

INSTANTIATE_TEST_SUITE_P(
    EntryPoints, KeccakEntryPoints,
    ::testing::Values(&monad_keccak256, &monad_keccak256_nomemo),
    [](auto const &info) {
        return info.param == &monad_keccak256 ? "memo" : "nomemo";
    });

TEST_P(KeccakEntryPoints, empty_input)
{
    EXPECT_EQ(
        digest_with(GetParam(), nullptr, 0), reference_keccak256(nullptr, 0));
}

// Cover short inputs, every XOR-count boundary, padding and full blocks.
TEST_P(KeccakEntryPoints, lengths_alignments_and_patterns)
{
    alignas(8) std::array<uint8_t, max_input_length + 7> buffer{};
    for (unsigned pattern = 0; pattern < 3; ++pattern) {
        for (size_t alignment_offset = 0; alignment_offset < 8;
             ++alignment_offset) {
            auto *const input = buffer.data() + alignment_offset;
            fill_pattern(input, pattern);
            for (size_t input_length = 0; input_length <= max_input_length;
                 ++input_length) {
                ASSERT_EQ(
                    digest_with(GetParam(), input, input_length),
                    reference_keccak256(input, input_length))
                    << "length=" << input_length
                    << ", alignment=" << alignment_offset
                    << ", pattern=" << pattern;
            }
        }
    }
}

// Callers hash a buffer into itself (keccak_inplace_to_root_hash).
TEST_P(KeccakEntryPoints, output_aliases_input)
{
    for (size_t const input_length :
         {0u, 1u, 31u, 32u, 33u, 135u, 136u, 137u, 532u, 544u}) {
        std::array<uint8_t, max_input_length> buffer;
        std::memcpy(buffer.data(), longer.data(), buffer.size());
        auto const expected = reference_keccak256(buffer.data(), input_length);
        GetParam()(buffer.data(), input_length, buffer.data());
        ASSERT_TRUE(std::equal(expected.begin(), expected.end(), buffer.data()))
            << "length=" << input_length;
    }
}

// The buffers above extend past every input, which hides a read outside it.
// Place inputs flush against an inaccessible page on either side instead.
TEST_P(KeccakEntryPoints, reads_stay_inside_input)
{
    auto const page_size = static_cast<size_t>(sysconf(_SC_PAGESIZE));
    ASSERT_GE(page_size, max_input_length);
    void *const mapping = mmap(
        nullptr, 3 * page_size, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    ASSERT_NE(mapping, MAP_FAILED);
    auto *const page = static_cast<uint8_t *>(mapping) + page_size;
    ASSERT_EQ(mprotect(page, page_size, PROT_READ | PROT_WRITE), 0);
    for (size_t i = 0; i < page_size; ++i) {
        page[i] = static_cast<uint8_t>(i * 37 + 11);
    }
    uint8_t const *const page_begin = page;
    uint8_t const *const page_end = page + page_size;
    for (size_t input_length = 0; input_length <= max_input_length;
         ++input_length) {
        for (uint8_t const *const input :
             {page_begin, page_end - input_length}) {
            ASSERT_EQ(
                digest_with(GetParam(), input, input_length),
                reference_keccak256(input, input_length))
                << "length=" << input_length
                << ", page offset=" << input - page_begin;
        }
    }
    ASSERT_EQ(munmap(mapping, 3 * page_size), 0);
}

// Every remainder, input alignment and pattern: misses followed by hits.
TEST(KeccakMemo, misses_then_hits)
{
    reset();
    check(nullptr, 0);
    check(nullptr, 0);
    require(
        recorded_entry_count == 1, "empty-input hit inserted another entry");

    alignas(8) std::array<uint8_t, max_input_length + 7> buffer{};
    for (unsigned pattern = 0; pattern < 3; ++pattern) {
        for (size_t alignment_offset = 0; alignment_offset < 8;
             ++alignment_offset) {
            auto *const input = buffer.data() + alignment_offset;
            fill_pattern(input, pattern);
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
}

TEST(KeccakMemo, dishonest_hints)
{
    // Honest and dishonest hints at every length and alignment.
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
}

TEST(KeccakMemo, capacity_only_mismatch)
{
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
}

// The mirror of capacity_only_mismatch: the published entry has the non-zero
// capacity, and a digest's first state, whose capacity is zero, has its rate.
TEST(KeccakMemo, first_state_capacity_mismatch)
{
    reset();
    check(longer.data(), KECCAK_RATE);
    // Choose a second block that turns entry 0's output rate into a padded
    // five-byte message: entry 2 then has that rate over a non-zero capacity.
    uint8_t const message[5] = {1, 2, 3, 4, 5};
    std::array<uint8_t, KECCAK_RATE> padded{};
    std::memcpy(padded.data(), message, sizeof(message));
    padded[sizeof(message)] = 0x01;
    padded[KECCAK_RATE - 1] = 0x80;
    std::array<uint8_t, 2 * KECCAK_RATE> input;
    std::memcpy(input.data(), longer.data(), KECCAK_RATE);
    auto const *const output_rate =
        reinterpret_cast<uint8_t const *>(keccakf_memo[0].out);
    for (size_t i = 0; i < KECCAK_RATE; ++i) {
        input[KECCAK_RATE + i] =
            static_cast<uint8_t>(padded[i] ^ output_rate[i]);
    }
    check(input.data(), input.size());
    require(
        std::memcmp(keccakf_memo[2].in, padded.data(), KECCAK_RATE) == 0,
        "fixture rate is not the padded message");
    State const zero{};
    require(
        std::memcmp(keccakf_memo[2].in + 17, zero.data(), 64) != 0,
        "fixture has a zero capacity");

    hint_mode = Hint::Mismatch;
    mismatch_index = 2;
    size_t const permutations = permutation_count;
    // As the only block of a digest, then as the first of two.
    check(message, sizeof(message));
    check(padded.data(), padded.size());
    require(
        permutation_count == permutations + 3,
        "accepted an entry with a different capacity");
}

// A state that differs from a published input in any one byte must miss.
// Drive the policy directly: a sponge cannot choose its capacity.
TEST(KeccakMemo, single_byte_mismatch)
{
    reset();
    State base;
    std::memcpy(base.data(), longer.data(), KECCAKF_STATE_BYTES);
    auto const permute = [](State const &input) {
        KeccakMemo<Executor> policy;
        uint64_t *const state = policy.first();
        std::memcpy(state, input.data(), KECCAKF_STATE_BYTES);
        uint64_t const *const output = policy.permute(state);
        policy.finish(state);
        return output;
    };
    permute(base);
    require(recorded_entry_count == 1, "fixture was not published");
    for (size_t byte = 0; byte < KECCAKF_STATE_BYTES; ++byte) {
        State probe = base;
        reinterpret_cast<uint8_t *>(probe.data())[byte] ^= 0x01;
        hint_mode = Hint::Mismatch;
        uint64_t const *const output = permute(probe);
        require(
            output != keccakf_memo[0].out && recorded_entry_count == 2,
            std::format("accepted a state that differs in byte {}", byte));
        verify_entries(0);
        truncate(1);
    }
    hint_mode = Hint::Mismatch;
    require(
        permute(base) == keccakf_memo[0].out && recorded_entry_count == 1,
        "rejected an identical state");
}

// Inputs that extend earlier ones hit on the blocks they share and compute
// the rest, on the general path and on the 532-byte one.
TEST(KeccakMemo, shared_prefixes)
{
    reset();
    // Each length, then the permutations left to run after the hits.
    for (auto const &[input_length, expected_permutations] :
         std::initializer_list<std::pair<size_t, size_t>>{
             {136, 2},
             {137, 1},
             {272, 2},
             {408, 2},
             {532, 1},
             {544, 2},
             {1088, 5},
             {1089, 1},
             {532, 0}}) {
        size_t const permutations = permutation_count;
        check(longer.data(), input_length);
        require(
            permutation_count == permutations + expected_permutations,
            std::format("shared prefix: length={}", input_length));
    }
}

// A lie about a digest's first state ends its lookups, so dishonest_hints
// never lies about a later one. Lie only after some hits.
TEST(KeccakMemo, dishonest_hint_after_hits)
{
    for (auto const mode :
         {Hint::Missing, Hint::OutOfRange, Hint::Unpublished, Hint::Mismatch}) {
        for (size_t const input_length : {272u, 532u, 1088u}) {
            size_t const states = input_length / KECCAK_RATE + 1;
            for (size_t hits = 1; hits < states; ++hits) {
                reset();
                uint8_t const seed = 0x42;
                check(&seed, 1);
                check(longer.data(), input_length);
                size_t const permutations = permutation_count;
                size_t const lookups = hint_lookup_count;
                honest_lookup_count = hits;
                hint_mode = mode;
                check(longer.data(), input_length);
                require(
                    permutation_count == permutations + states - hits,
                    "did not recompute every state from the lie on");
                require(
                    hint_lookup_count == lookups + hits + 1,
                    "expected a lookup per hit and one for the lie");
                check(nullptr, 0);
            }
        }
    }
}

TEST(KeccakMemo, full_table)
{
    // Cross the end of the table with five down to zero free entries. Both
    // lengths need four permutations, including padding.
    reset();
    for (size_t used_entries = KECCAKF_MEMO_ENTRIES - 5;
         used_entries <= KECCAKF_MEMO_ENTRIES;
         ++used_entries) {
        size_t const free_entries = KECCAKF_MEMO_ENTRIES - used_entries;
        fill_to(used_entries);
        for (size_t const input_length : {408u, 532u}) {
            truncate(used_entries);
            check(longer.data(), input_length);
            require(
                recorded_entry_count ==
                    used_entries + (free_entries < 4 ? free_entries : 4),
                "unexpected insertion count at capacity boundary");
            check(longer.data(), input_length);
            check(nullptr, 0);
        }
        truncate(used_entries);
    }
    verify_entries(0);

    // Leave one free entry: the next digest fills it on its first block and
    // must use the spare for the rest, without modifying published entries.
    truncate(KECCAKF_MEMO_ENTRIES - 1);
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
        // Published entries remain usable when full: entry 3 is fill input 3.
        uint32_t const cached = 3;
        hint_mode = Hint::Find;
        size_t const lookups = hint_lookup_count;
        size_t const permutations = permutation_count;
        check(&cached, sizeof(cached));
        require(hint_lookup_count == lookups + 1, "full table skipped lookup");
        require(
            permutation_count == permutations,
            "full table recomputed a published entry");
    }
    verify_entries(0);

    // The bytecode entry point must neither query nor populate the memo.
    for (bool const table_full : {true, false}) {
        if (!table_full) {
            reset();
        }
        size_t const initial_lookup_count = hint_lookup_count;
        size_t const entries = recorded_entry_count;
        for (size_t const input_length : lengths) {
            std::array<uint8_t, 32> actual{};
            keccak256_nomemo<Executor>(
                longer.data() + 1, input_length, actual.data());
            auto const expected =
                reference_keccak256(longer.data() + 1, input_length);
            require(actual == expected, "non-memo digest mismatch");
        }
        require(
            hint_lookup_count == initial_lookup_count &&
                recorded_entry_count == entries,
            "bytecode path touched the memo");
    }
}
