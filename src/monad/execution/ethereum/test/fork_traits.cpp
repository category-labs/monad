#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>

#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/block_reward.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <test_resource_data.h>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::fork_traits;

using db_t = db::InMemoryTrieDB;

constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};
constexpr auto b{0x5353535353535353535353535353535353535353_address};
constexpr auto c{0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address};

TEST(fork_traits, frontier)
{
    Transaction t{};
    EXPECT_EQ(intrinsic_gas<fork_traits::frontier>(t), 21'000);

    t.data.push_back(0x00);
    EXPECT_EQ(intrinsic_gas<fork_traits::frontier>(t), 21'004);

    t.data.push_back(0xff);
    EXPECT_EQ(intrinsic_gas<fork_traits::frontier>(t), 21'072);

    db_t db;
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});
    {
        BlockState bs;
        State s{bs, db};

        EXPECT_TRUE(s.account_exists(a));

        // gas price
        EXPECT_EQ(
            gas_price<fork_traits::frontier>(
                Transaction{.max_fee_per_gas = 1'000}, 0u),
            1'000);

        // txn award
        EXPECT_EQ(
            calculate_txn_award<fork_traits::frontier>(
                Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
            uint256_t{9'000'000'000'000'000'000});
    }
    {
        // block award
        BlockState bs;
        State s{bs, db};
        Block block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        apply_block_reward(
            bs,
            db,
            block,
            fork_traits::frontier::block_reward,
            fork_traits::frontier::additional_ommer_reward);
        db.commit(s.block_state_.state, s.block_state_.code);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(a)),
            5'312'500'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(b)),
            4'375'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(c)),
            3'750'000'000'000'000'000);
    }
}

TEST(fork_traits, homestead)
{
    Transaction t{};
    EXPECT_EQ(intrinsic_gas<fork_traits::homestead>(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(intrinsic_gas<fork_traits::homestead>(t), 21'000);
}

TEST(fork_traits, spurious_dragon)
{
    Transaction t{};
    EXPECT_EQ(intrinsic_gas<fork_traits::spurious_dragon>(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(intrinsic_gas<fork_traits::spurious_dragon>(t), 21'000);

    db_t db;
    db.commit(
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{});

    BlockState bs;
    State s{bs, db};
    s.add_to_balance(a, 0);
    s.destruct_touched_dead();

    EXPECT_FALSE(s.account_exists(a));
}

TEST(fork_traits, byzantium)
{
    Transaction t{};
    EXPECT_EQ(intrinsic_gas<fork_traits::byzantium>(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(intrinsic_gas<fork_traits::byzantium>(t), 21'000);

    db_t db;
    BlockState bs;
    State as{bs, db};
    (void)as.get_balance(a);

    EXPECT_FALSE(as.account_exists(a));

    // block award
    Block block{
        .header = {.number = 10, .beneficiary = a},
        .transactions = {},
        .ommers = {
            BlockHeader{.number = 9, .beneficiary = b},
            BlockHeader{.number = 8, .beneficiary = c}}};
    apply_block_reward(
        bs,
        db,
        block,
        fork_traits::byzantium::block_reward,
        fork_traits::byzantium::additional_ommer_reward);
    State cs{bs, db};
    EXPECT_EQ(
        intx::be::load<uint256_t>(cs.get_balance(a)),
        3'187'500'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(cs.get_balance(b)),
        2'625'000'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(cs.get_balance(c)),
        2'250'000'000'000'000'000);
}

static_assert(
    std::derived_from<
        fork_traits::constantinople_and_petersburg, fork_traits::byzantium>);
static_assert(std::same_as<
              fork_traits::constantinople_and_petersburg::next_fork_t,
              fork_traits::istanbul>);
TEST(fork_traits, constantinople_and_petersburg)
{
    // block award
    db_t db;
    BlockState bs;
    State s{bs, db};

    Block block{
        .header = {.number = 10, .beneficiary = a},
        .transactions = {},
        .ommers = {
            BlockHeader{.number = 9, .beneficiary = b},
            BlockHeader{.number = 8, .beneficiary = c}}};
    apply_block_reward(
        bs,
        db,
        block,
        fork_traits::constantinople_and_petersburg::block_reward,
        fork_traits::constantinople_and_petersburg::additional_ommer_reward);

    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(a)), 2'125'000'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(b)), 1'750'000'000'000'000'000);
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(c)), 1'500'000'000'000'000'000);
}

static_assert(
    std::derived_from<
        fork_traits::istanbul, fork_traits::constantinople_and_petersburg>);
static_assert(
    std::same_as<fork_traits::istanbul::next_fork_t, fork_traits::berlin>);
TEST(fork_traits, istanbul)
{
    Transaction t{};
    EXPECT_EQ(intrinsic_gas<fork_traits::istanbul>(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    t.data.push_back(0x00);
    EXPECT_EQ(intrinsic_gas<fork_traits::istanbul>(t), 21'004);

    t.data.push_back(0xff);
    EXPECT_EQ(intrinsic_gas<fork_traits::istanbul>(t), 21'020);
}

TEST(fork_traits, berlin)
{
    Transaction t{};
    EXPECT_EQ(intrinsic_gas<fork_traits::berlin>(t), 53'000);

    t.to = 0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address;
    EXPECT_EQ(intrinsic_gas<fork_traits::berlin>(t), 21'000);

    static constexpr auto key1{
        0x0000000000000000000000000000000000000000000000000000000000000007_bytes32};
    static constexpr auto key2{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    t.access_list.push_back({*t.to, {key1, key2}});
    EXPECT_EQ(
        intrinsic_gas<fork_traits::berlin>(t), 21'000 + 2400 + 1900 + 1900);

    t.data.push_back(0x00);
    t.data.push_back(0xff);
    EXPECT_EQ(intrinsic_gas<fork_traits::berlin>(t), 27'220);
}

TEST(fork_traits, london)
{
    db_t db;
    BlockState bs;
    State s{bs, db};

    // gas price
    Transaction t1{
        .max_fee_per_gas = 3'000,
        .type = TransactionType::eip155,
        .max_priority_fee_per_gas = 1'000};
    Transaction t2{.max_fee_per_gas = 3'000, .type = TransactionType::eip155};
    Transaction t3{
        .max_fee_per_gas = 5'000,
        .type = TransactionType::eip1559,
        .max_priority_fee_per_gas = 1'000};
    Transaction t4{.max_fee_per_gas = 5'000, .type = TransactionType::eip1559};
    Transaction t5{
        .max_fee_per_gas = 5'000,
        .type = TransactionType::eip1559,
        .max_priority_fee_per_gas = 4'000};
    EXPECT_EQ(gas_price<fork_traits::london>(t1, 2'000u), 3'000);
    EXPECT_EQ(gas_price<fork_traits::london>(t2, 2'000u), 3'000);
    EXPECT_EQ(gas_price<fork_traits::london>(t3, 2'000u), 3'000);
    EXPECT_EQ(gas_price<fork_traits::london>(t4, 2'000u), 2'000);
    EXPECT_EQ(gas_price<fork_traits::london>(t5, 2'000u), 5'000);

    // txn award
    EXPECT_EQ(
        calculate_txn_award<fork_traits::london>(
            Transaction{.max_fee_per_gas = 100'000'000'000}, 0, 90'000'000),
        uint256_t{9'000'000'000'000'000'000});
}

// EIP-3675
TEST(fork_traits, paris_apply_block_reward)
{
    Block block{};
    block.header.beneficiary = a;
    db_t db{};
    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}}},
        Code{});

    {
        db_t db;
        BlockState bs;
        State s{bs, db};

        apply_block_reward(
            bs,
            db,
            block,
            fork_traits::paris::block_reward,
            fork_traits::paris::additional_ommer_reward);

        EXPECT_EQ(intx::be::load<uint256_t>(s.get_balance(a)), 0u);
    }
    {
        db_t db;
        BlockState bs;
        State s{bs, db};

        apply_block_reward(
            bs,
            db,
            block,
            fork_traits::london::block_reward,
            fork_traits::london::additional_ommer_reward);

        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(a)),
            fork_traits::constantinople_and_petersburg::block_reward);
    }
}

// EIP-3860
TEST(fork_traits, shanghai_contract_creation_cost)
{
    byte_string data;
    for (auto i = 0u; i < uint64_t{0x80}; ++i) {
        data += {0xc0};
    }

    Transaction t{.data = data};

    EXPECT_EQ(
        intrinsic_gas<fork_traits::shanghai>(t),
        32'000u + 21'000u + 16u * 128u + 0u + 4u * 2u);
}
