#include <monad/contract/storage_array.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/contract/uint256.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/staking/types.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>

#include <test_resource_data.h>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::test;

struct Storage : public ::testing::Test
{
    static constexpr auto ADDRESS{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    OnDiskMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    BlockState bs{tdb};
    State state{bs, Incarnation{0, 0}};

    void SetUp() override
    {
        commit_sequential(
            tdb,
            StateDeltas{
                {ADDRESS,
                 StateDelta{
                     .account =
                         {std::nullopt, Account{.balance = 1, .nonce = 1}}}}},
            Code{},
            BlockHeader{});
        state.touch(ADDRESS);
    }
};

TEST_F(Storage, variable)
{
    StorageVariable<uint256_t> var(state, ADDRESS, bytes32_t{6000});
    ASSERT_FALSE(var.load().has_value());
    var.store(5);
    ASSERT_TRUE(var.load().has_value());
    EXPECT_EQ(var.load().value(), 5);
    var.store(2000);
    EXPECT_EQ(var.load().value(), 2000);
    var.clear();
    EXPECT_FALSE(var.load().has_value());
}

TEST_F(Storage, struct)
{
    struct S
    {
        int x;
        int y;
        uint256_t z;
    };

    StorageVariable<S> var(state, ADDRESS, bytes32_t{6000});

    ASSERT_FALSE(var.load().has_value());
    var.store(S{.x = 4, .y = 5, .z = 6});
    ASSERT_TRUE(var.load().has_value());
    S s = var.load().value();
    EXPECT_EQ(s.x, 4);
    EXPECT_EQ(s.y, 5);
    EXPECT_EQ(s.z, uint256_t(6));
    s.x *= 2;
    s.y *= 2;
    s.z *= 2;
    var.store(s);
    ASSERT_TRUE(var.load().has_value());
    S s2 = var.load().value();
    EXPECT_EQ(s2.x, 8);
    EXPECT_EQ(s2.y, 10);
    EXPECT_EQ(s2.z, 12);
    var.clear();
    EXPECT_FALSE(var.load().has_value());
}

TEST_F(Storage, array)
{
    struct SomeType
    {
        uint256_t blob;
        uint32_t counter;
    };

    StorageArray<SomeType> arr(state, ADDRESS, bytes32_t{100});
    EXPECT_EQ(arr.length(), 0);

    for (uint32_t i = 0; i < 100; ++i) {
        arr.push(SomeType{.blob = uint256_t{}, .counter = i});
        EXPECT_EQ(arr.length(), i + 1);
    }

    for (uint32_t i = 0; i < 100; ++i) {
        auto const res = arr.get(i);
        ASSERT_TRUE(res.load().has_value());
        EXPECT_EQ(res.load().value().counter, i);
    }

    for (uint32_t i = 100; i > 0; --i) {
        arr.pop();
        EXPECT_EQ(arr.length(), i - 1);
    }
}

TEST_F(Storage, uint256)
{
    bytes32_t y{5};
    Uint256BE be = std::bit_cast<Uint256BE>(y);
    auto const res = be.native().add(5).to_be();
    EXPECT_EQ(std::bit_cast<bytes32_t>(res), bytes32_t{10});
}
