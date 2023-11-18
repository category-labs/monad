#include <monad/core/account.hpp>
#include <monad/core/int.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/block_processor.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/test/make_db.hpp>

#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <optional>
#include <vector>

using namespace monad;

using db_t = db::InMemoryTrieDB;

TEST(BlockProcessor, shanghai_withdrawal)
{
    static constexpr auto a =
        0x5353535353535353535353535353535353535353_address;
    static constexpr auto b =
        0xbebebebebebebebebebebebebebebebebebebebe_address;

    std::optional<std::vector<Withdrawal>> withdrawals{};
    Withdrawal const w1 = {
        .index = 0, .validator_index = 0, .amount = 100u, .recipient = a};
    Withdrawal const w2 = {
        .index = 1, .validator_index = 0, .amount = 300u, .recipient = a};
    Withdrawal const w3 = {
        .index = 2, .validator_index = 0, .amount = 200u, .recipient = b};
    withdrawals = {w1, w2, w3};

    auto db = test::make_db<db_t>();

    db.commit(
        StateDeltas{
            {a, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}},
            {b, StateDelta{.account = {std::nullopt, Account{.balance = 0}}}}},
        Code{});

    BlockState bs{db};

    State state{bs};
    BlockProcessor::process_withdrawal(state, withdrawals);

    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(a)),
        uint256_t{400u} * uint256_t{1'000'000'000u});
    EXPECT_EQ(
        intx::be::load<uint256_t>(state.get_balance(b)),
        uint256_t{200u} * uint256_t{1'000'000'000u});
}

TEST(BlockProcessor, transfer_balance_dao)
{
    static constexpr auto individual = 100u;
    static constexpr auto total = individual * 116u;

    db_t db{};

    StateDeltas state_deltas{};

    for (auto const addr : dao::child_accounts) {
        Account a{.balance = individual};
        state_deltas.emplace(addr, StateDelta{.account = {std::nullopt, a}});
    }
    state_deltas.emplace(
        dao::withdraw_account,
        StateDelta{.account = {std::nullopt, Account{.balance = 0}}});

    db.commit(state_deltas, Code{});

    BlockState bs{db};

    BlockProcessor::transfer_balance_dao(bs);

    State s{bs};
    for (auto const &addr : dao::child_accounts) {
        EXPECT_EQ(intx::be::load<uint256_t>(s.get_balance(addr)), 0u);
    }
    EXPECT_EQ(
        intx::be::load<uint256_t>(s.get_balance(dao::withdraw_account)), total);
}
