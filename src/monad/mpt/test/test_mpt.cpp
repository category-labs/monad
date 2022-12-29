#include "mock_database.hpp"
#include "util.hpp"
#include <monad/mpt/merkle_patricia_tree.hpp>
#include <gtest/gtest.h>

using namespace monad::mpt;
using namespace monad::test_util;

namespace
{
struct TestInitializer
{
    std::vector<monad::mpt::KeyVal> const plain_state_;
    decltype(plain_state_.begin()) it_;
    uint64_t block_number_;

    TestInitializer(std::initializer_list<monad::mpt::KeyVal> list, uint64_t block_number)
        : plain_state_(list)
        , it_(plain_state_.begin())
        , block_number_(block_number)
    {
    }

    bool done() const
    {
        return it_ == plain_state_.end();
    }

    monad::mpt::KeyVal operator()()
    {
        assert(!done());
        return *it_++;
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
        {Path(to_nibbles({0x0a, 0x07, 0x0f, 0x09, 0x03, 0x06, 0x05})), {}},
        {Path(to_nibbles({0x0a, 0x07, 0x07, 0x0d, 0x03, 0x09, 0x07})), {}},
    }, 123456789);

    MerklePatriciaTree<MockDatabase> tree(initializer);
}
