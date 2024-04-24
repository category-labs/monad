#include "gtest/gtest.h"

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <monad/core/byte_string.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <cstdint>
#include <utility>
#include <vector>

using namespace ::monad::test;

template <typename TFixture>
struct TrieTest : public TFixture
{
};

using TrieTypes = ::testing::Types<InMemoryTrieGTest, OnDiskTrieGTest>;
TYPED_TEST_SUITE(TrieTest, TrieTypes);

TYPED_TEST(TrieTest, find_min_max_block_num)
{
    uint64_t const number_of_blocks = 128;
    std::vector<monad::byte_string> blocknums;
    blocknums.reserve(number_of_blocks);
    std::vector<Update> update_vec;
    for (uint64_t i = 0; i < number_of_blocks; ++i) {
        blocknums.push_back(serialize_as_big_endian<BLOCK_NUM_BYTES>(i));
        update_vec.push_back(Update{
            .key = blocknums.back(),
            .value = monad::byte_string_view{},
            .incarnation = false,
            .next = {}});
    }
    this->root = upsert_vector(this->aux, *this->sm, {}, std::move(update_vec));

    Nibbles min_block = find_min_key_blocking(this->aux, *this->root);
    EXPECT_EQ(min_block.nibble_size(), 12);
    EXPECT_EQ(min_block, NibblesView{blocknums[0]});
    Nibbles max_block = find_max_key_blocking(this->aux, *this->root);
    EXPECT_EQ(max_block.nibble_size(), 12);
    EXPECT_EQ(max_block, NibblesView{blocknums.back()});

    // erase the first 10 blocks
    update_vec.clear();
    for (uint64_t i = 0; i < 10; ++i) {
        update_vec.push_back(make_erase(blocknums[i]));
    }
    this->root = upsert_vector(
        this->aux, *this->sm, std::move(this->root), std::move(update_vec));

    min_block = find_min_key_blocking(this->aux, *this->root);
    EXPECT_EQ(min_block, NibblesView{blocknums[10]});
    max_block = find_max_key_blocking(this->aux, *this->root);
    EXPECT_EQ(max_block, NibblesView{blocknums.back()});
}
