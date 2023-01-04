#include <gtest/gtest.h>
#include <gmock/gmock-matchers.h>

#include "mock_database.hpp"
#include "monad/core/byte_string.hpp"
#include "util.hpp"

#include <monad/mpt/merkle_patricia_tree.hpp>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test_util;

namespace
{
struct TestInitializer
{
    std::vector<monad::mpt::KeyVal> const state_;
    size_t index_;
    uint64_t block_number_;

    TestInitializer(std::vector<monad::mpt::KeyVal>&& state, uint64_t block_number)
        : state_(std::move(state))
        , index_(0)
        , block_number_(block_number)
    {
    }

    bool done() const
    {
        return index_ == state_.size();
    }

    std::optional<monad::mpt::KeyVal> operator()()
    {
        if (MONAD_UNLIKELY(done())) {
            return std::nullopt;
        }

        return state_[index_++];
    }

    uint64_t block_number() const
    {
        return block_number_;
    }
};
} // namespace

TEST(MptStructure, Sanity)
{
    TestInitializer initializer(
    {
        {Path(to_nibbles({0x0a, 0x07, 0x01, 0x01, 0x03, 0x05, 0x05})), {}},
        {Path(to_nibbles({0x0a, 0x07, 0x07, 0x0d, 0x03, 0x03, 0x07})), {}},
        {Path(to_nibbles({0x0a, 0x07, 0x07, 0x0d, 0x03, 0x09, 0x07})), {}},
        {Path(to_nibbles({0x0a, 0x07, 0x0f, 0x09, 0x03, 0x06, 0x05})), {}},
    }, 123456789);

    MockDatabaseKey storage;

    EXPECT_NO_THROW(MerklePatriciaTree tree(initializer, storage));

    auto const block = monad::to_big_endian_byte_string(initializer.block_number()); 

    MockDatabaseKey::rep const expected = {
        byte_string{0x0a, 0x07, 0x01} + block,
        byte_string{0x0a, 0x07, 0x07, 0x0d, 0x03, 0x03} + block,
        byte_string{0x0a, 0x07, 0x07, 0x0d, 0x03, 0x09} + block,
        byte_string{0x0a, 0x07, 0x07, 0x0d, 0x03} + block,
        byte_string{0x0a, 0x07, 0x07} + block,
        byte_string{0x0a, 0x07, 0x0f} + block,
        byte_string{0x0a, 0x07} + block,
        byte_string{} + block,
    };

    // keys should be inserted in increasing order
    EXPECT_TRUE(std::ranges::equal(storage, expected));
}
