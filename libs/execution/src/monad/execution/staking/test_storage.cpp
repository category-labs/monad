#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/staking/storage.hpp>
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

TEST_F(Storage, one_int)
{
    StorageAdapter<uint64_t> writer;
    StorageAdapter<uint64_t> reader;
    static_assert(StorageAdapter<uint64_t>::N == 1u);

    auto const key = bytes32_t{};
    auto &b = writer.typed;
    b = 1000;
    state.set_storage(ADDRESS, key, writer.slots[0]);

    reader.slots[0] = state.get_storage(ADDRESS, key);
    EXPECT_EQ(reader.typed, 1000);
}

TEST_F(Storage, one_byte32)
{
    StorageAdapter<bytes32_t> writer;
    StorageAdapter<bytes32_t> reader;
    static_assert(StorageAdapter<uint64_t>::N == 1u);

    auto const key = bytes32_t{};
    auto &b = writer.typed;
    b = bytes32_t{1000};
    state.set_storage(ADDRESS, key, writer.slots[0]);

    reader.slots[0] = state.get_storage(ADDRESS, key);
    EXPECT_EQ(reader.typed, bytes32_t{1000});
}

TEST_F(Storage, spans_two_slots_aligned)
{
    struct Pair
    {
        uint256_t x;
        uint256_t y;
    };

    StorageAdapter<Pair> writer;
    StorageAdapter<Pair> reader;
    static_assert(StorageAdapter<Pair>::N == 2u);

    auto &mystruct = writer.typed;
    mystruct.x = 1000;
    mystruct.y = 2000;
    state.set_storage(ADDRESS, bytes32_t{}, writer.slots[0]);
    state.set_storage(ADDRESS, bytes32_t{1}, writer.slots[1]);

    reader.slots[0] = state.get_storage(ADDRESS, bytes32_t{});
    reader.slots[1] = state.get_storage(ADDRESS, bytes32_t{1});
    EXPECT_EQ(reader.typed.x, 1000);
    EXPECT_EQ(reader.typed.y, 2000);
}

TEST_F(Storage, spans_two_slots_unaligned)
{
    struct SomeType
    {
        Address first;
        Address second;
        bool flag;
    };

    StorageAdapter<SomeType> writer;
    StorageAdapter<SomeType> reader;
    static_assert(StorageAdapter<SomeType>::N == 2u);

    auto &mystruct = writer.typed;
    mystruct.first = ADDR_A;
    mystruct.second = ADDR_B;
    mystruct.flag = true;
    state.set_storage(ADDRESS, bytes32_t{}, writer.slots[0]);
    state.set_storage(ADDRESS, bytes32_t{1}, writer.slots[1]);

    reader.slots[0] = state.get_storage(ADDRESS, bytes32_t{});
    reader.slots[1] = state.get_storage(ADDRESS, bytes32_t{1});
    EXPECT_EQ(reader.typed.first, ADDR_A);
    EXPECT_EQ(reader.typed.second, ADDR_B);
    EXPECT_TRUE(reader.typed.flag);
}
