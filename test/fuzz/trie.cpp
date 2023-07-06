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

template <typename TFixture>
struct trie_fuzzer_fixture
    : public ::fuzztest::PerIterationFixtureAdapter<TFixture>
{
    using TFixture::process_updates;
    using TFixture::trie_;

    void OneHundredUpdates(
        std::array<size_t, 100> const &groups,
        std::map<size_t, std::optional<monad::byte_string>> const &mods)
    {
        Process(one_hundred_updates, groups, mods);

        if (!mods.empty()) {
            // Fix the trie so that the root hashes are back to normal
            std::vector<Update> correct;
            for (auto const &[i, _] : mods) {
                correct.emplace_back(make_upsert(
                    one_hundred_updates[i].first,
                    one_hundred_updates[i].second));
            }
            process_updates(correct);
        }

        EXPECT_EQ(
            trie_.root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes32);
    }

    void GeneratedKv(
        std::map<monad::byte_string, monad::byte_string> const &kv,
        std::vector<size_t> const &groups,
        std::map<size_t, std::optional<monad::byte_string>> const &mods)
    {
        std::vector<std::pair<bytes32_t, byte_string>> transformed;
        for (auto const &p : kv) {
            transformed.emplace_back(
                [&]() {
                    MONAD_ASSERT(p.first.size() == sizeof(bytes32_t));
                    bytes32_t b;
                    std::copy_n(p.first.data(), sizeof(bytes32_t), b.bytes);
                    return b;
                }(),
                p.second);
        }
        Process(transformed, groups, mods);

        std::vector<Update> updates;
        for (size_t i = 0; i < transformed.size(); ++i) {
            if (mods.contains(i) && !mods.at(i).has_value()) {
                continue;
            }
            updates.emplace_back(make_del(transformed[i].first));
        }

        if (!updates.empty()) {
            process_updates(updates);
        }
        EXPECT_EQ(trie_.root_hash(), NULL_ROOT);
    }

    void Process(
        std::ranges::range auto const &kv,
        std::ranges::range auto const &groups,
        std::map<size_t, std::optional<monad::byte_string>> const &mods)
    {
        MONAD_ASSERT(groups.size() == kv.size());

        std::map<size_t, std::vector<Update>> inputs = {{kv.size(), {}}};

        for (size_t i = 0; i < groups.size(); ++i) {
            inputs[groups[i]].emplace_back(
                make_upsert(kv[i].first, kv[i].second));
        }

        // Add updates to the next batch of inputs to be processed
        for (size_t i = 0; i < kv.size(); ++i) {
            if (!mods.contains(i)) {
                continue;
            }

            auto const it = inputs.find(groups[i]);
            MONAD_DEBUG_ASSERT(it != inputs.end());

            auto const next = std::next(it);
            MONAD_DEBUG_ASSERT(next != inputs.end());

            if (mods.at(i).has_value()) {
                next->second.emplace_back(
                    make_upsert(kv[i].first, mods.at(i).value()));
            }
            else {
                next->second.emplace_back(make_del(kv[i].first));
            }
        }

        if (inputs[kv.size()].empty()) {
            inputs.erase(kv.size());
        }

        for (auto &[_, input] : inputs) {
            std::ranges::sort(input, std::less<>{}, trie::get_update_key);
            process_updates(input);
        }
    }
};

using rocks_single_trie_fixture_t =
    trie_fuzzer_fixture<rocks_fixture<PathComparator>>;

FUZZ_TEST_F(rocks_single_trie_fixture_t, OneHundredUpdates)
    .WithDomains(
        ArrayOf<one_hundred_updates.size()>(
            InRange(0ul, one_hundred_updates.size() - 1)),
        MapOf(
            InRange(0ul, one_hundred_updates.size() - 1),
            OptionalOf(Arbitrary<monad::byte_string>().WithMinSize(1))));

inline constexpr auto GENERATED_SIZE = 100ul;

// Note: depending on the GENERATED_SIZE, GeneratedKv may run out of stack
// memory. To permiss the test a larger stack, set the environment variable
// FUZZTEST_STACK_LIMIT.
FUZZ_TEST_F(rocks_single_trie_fixture_t, GeneratedKv)
    .WithDomains(
        MapOf(
            Arbitrary<monad::byte_string>().WithSize(sizeof(bytes32_t)),
            NonEmpty(Arbitrary<monad::byte_string>()))
            .WithSize(GENERATED_SIZE),
        VectorOf(InRange(0ul, GENERATED_SIZE - 1)).WithSize(GENERATED_SIZE),
        MapOf(
            InRange(0ul, GENERATED_SIZE - 1),
            OptionalOf(NonEmpty(Arbitrary<monad::byte_string>()))));
