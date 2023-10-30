#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/execution_model.hpp>

#include <monad/state2/state.hpp>

#include <monad/test/make_db.hpp>

#include <gtest/gtest.h>

#include <shared_mutex>

using namespace monad;

using mutex_t = std::shared_mutex;
using db_t = db::InMemoryTrieDB;
using state_t = State<mutex_t>;

TEST(BlockProcessor, shanghai_withdrawal)
{
    static constexpr auto a =
        0x5353535353535353535353535353535353535353_address;
    static constexpr auto b =
        0xbebebebebebebebebebebebebebebebebebebebe_address;

    std::optional<std::vector<Withdrawal>> withdrawals{};
    Withdrawal w1 = {
        .index = 0, .validator_index = 0, .amount = 100u, .recipient = a};
    Withdrawal w2 = {
        .index = 1, .validator_index = 0, .amount = 300u, .recipient = a};
    Withdrawal w3 = {
        .index = 2, .validator_index = 0, .amount = 200u, .recipient = b};
    withdrawals = {w1, w2, w3};

    auto db = test::make_db<db_t>();

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}},
            {b, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}}},
        Code{});

    BlockState<mutex_t> bs;

    state_t state{bs, db};
    AllTxnBlockProcessor::process_withdrawal(state, withdrawals);

    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(a)),
        uint256_t{400u} * uint256_t{1'000'000'000u});
    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(b)),
        uint256_t{200u} * uint256_t{1'000'000'000u});
}
