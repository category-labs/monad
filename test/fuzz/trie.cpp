#include <monad/core/byte_string.hpp>
#include <monad/test/one_hundred_updates.hpp>
#include <monad/test/trie_fixture.hpp>
#include <monad/trie/in_memory_comparator.hpp>

#include <fuzztest/fuzztest.h>
#include <fuzztest/googletest_fixture_adapter.h>
#include <gtest/gtest.h>

using namespace fuzztest;
using namespace monad;
using namespace monad::test;
using namespace monad::trie;

constexpr auto const &UPDATES = one_hundred_updates;
constexpr auto const SENTINEL = UPDATES.size();

template <typename TFixture>
struct trie_fuzzer_fixture
    : public ::fuzztest::PerIterationFixtureAdapter<TFixture>
{
    using TFixture::process_updates;
    using TFixture::trie_;

    void TrieRootMatches(
        std::array<size_t, UPDATES.size()> const &groups,
        std::map<size_t, std::optional<monad::byte_string>> const &mods)
    {
        std::map<size_t, std::vector<Update>> inputs = {{SENTINEL, {}}};

        for (size_t i = 0; i < groups.size(); ++i) {
            inputs[groups[i]].emplace_back(
                make_upsert(UPDATES[i].first, UPDATES[i].second));
        }

        // Add updates to the next batch of inputs to be processed
        for (size_t i = 0; i < UPDATES.size(); ++i) {
            if (!mods.contains(i)) {
                continue;
            }

            auto const it = inputs.find(groups[i]);
            MONAD_DEBUG_ASSERT(it != inputs.end());

            auto const next = std::next(it);
            MONAD_DEBUG_ASSERT(next != inputs.end());

            if (mods.at(i).has_value()) {
                next->second.emplace_back(
                    make_upsert(UPDATES[i].first, mods.at(i).value()));
            }
            else {
                next->second.emplace_back(make_del(UPDATES[i].first));
            }
        }

        if (inputs[SENTINEL].empty()) {
            inputs.erase(SENTINEL);
        }

        for (auto &[_, input] : inputs) {
            std::ranges::sort(input, std::less<>{}, trie::get_update_key);
            process_updates(input);
        }

        if (!mods.empty()) {
            // Fix the trie so that the root hashes are back to normal
            std::vector<Update> correct;
            for (auto const &[i, _] : mods) {
                correct.emplace_back(
                    make_upsert(UPDATES[i].first, UPDATES[i].second));
            }
            process_updates(correct);
        }

        EXPECT_EQ(
            trie_.root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes32);
    }
};

using in_memory_single_trie_fixture_t =
    trie_fuzzer_fixture<in_memory_fixture<InMemoryPathComparator>>;

using rocks_single_trie_fixture_t =
    trie_fuzzer_fixture<rocks_fixture<PathComparator>>;

inline auto UpdateDomain()
{
    return InRange(0ul, SENTINEL - 1);
}

FUZZ_TEST_F(in_memory_single_trie_fixture_t, TrieRootMatches)
    .WithDomains(
        ArrayOf<UPDATES.size()>(UpdateDomain()),
        MapOf(
            UpdateDomain(),
            OptionalOf(Arbitrary<monad::byte_string>().WithMinSize(1))));

FUZZ_TEST_F(rocks_single_trie_fixture_t, TrieRootMatches)
    .WithDomains(
        ArrayOf<UPDATES.size()>(UpdateDomain()),
        MapOf(
            UpdateDomain(),
            OptionalOf(Arbitrary<monad::byte_string>().WithMinSize(1))));
