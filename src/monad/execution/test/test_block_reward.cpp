#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <optional>

using namespace monad;

using db_t = db::TrieDb;

constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};
constexpr auto b{0x5353535353535353535353535353535353535353_address};
constexpr auto c{0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address};

TEST(BlockReward, apply_block_reward)
{
    // Frontier
    {
        db_t db{mpt::DbOptions{.on_disk = false}};
        db.commit(
            StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
            Code{});

        BlockState bs{db};
        State as{bs};

        EXPECT_TRUE(as.account_exists(a));

        Block const block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        apply_block_reward<EVMC_FRONTIER>(bs, block);

        State cs{bs};

        EXPECT_EQ(
            intx::be::load<uint256_t>(cs.get_balance(a)),
            5'312'500'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(cs.get_balance(b)),
            4'375'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(cs.get_balance(c)),
            3'750'000'000'000'000'000);
    }

    // Byzantium
    {
        db_t db{mpt::DbOptions{.on_disk = false}};
        BlockState bs{db};
        State as{bs};
        (void)as.get_balance(a);

        EXPECT_FALSE(as.account_exists(a));

        // block award
        Block const block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        apply_block_reward<EVMC_BYZANTIUM>(bs, block);

        State cs{bs};
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

    // Constantinople_and_petersburg
    {
        db_t db{mpt::DbOptions{.on_disk = false}};
        BlockState bs{db};
        State s{bs};

        Block const block{
            .header = {.number = 10, .beneficiary = a},
            .transactions = {},
            .ommers = {
                BlockHeader{.number = 9, .beneficiary = b},
                BlockHeader{.number = 8, .beneficiary = c}}};
        apply_block_reward<EVMC_PETERSBURG>(bs, block);

        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(a)),
            2'125'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(b)),
            1'750'000'000'000'000'000);
        EXPECT_EQ(
            intx::be::load<uint256_t>(s.get_balance(c)),
            1'500'000'000'000'000'000);
    }

    // Paris EIP-3675
    {
        Block block{};
        block.header.beneficiary = a;

        db_t db{mpt::DbOptions{.on_disk = false}};
        BlockState bs{db};
        State s{bs};

        apply_block_reward<EVMC_PARIS>(bs, block);

        EXPECT_EQ(intx::be::load<uint256_t>(s.get_balance(a)), 0u);
    }
}
