#include <monad/db/block_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/execution_model.hpp>

#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/value_state.hpp>

#include <test_resource_data.h>

#include <boost/fiber/all.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using state_t = fake::State;
using fork_t = fake::traits::alpha<state_t>;

using block_db_t = db::BlockDb;
using db_t = db::InMemoryTrieDB;
using account_state_t = state::AccountState<db_t>;
using value_state_t = state::ValueState<db_t>;
using code_state_t = state::CodeState<db_t>;
using real_state_t = state::State<
    account_state_t, value_state_t, code_state_t, block_db_t, db_t>;

/*
// TODO: Comment back when both BlockProcessor refactor & transfer_balance_dao
refactor are done

namespace
{
    constexpr auto individual = 100u;
    constexpr auto total = individual * 116u;
}
*/

template <class TState>
struct EmptyFiberData
{
    Receipt _result{};
    EmptyFiberData(
        TState &, Transaction const &, BlockHeader const &, unsigned int)
    {
    }
    Receipt get_receipt() { return _result; }
    inline void operator()() {}
};

template <class TState>
struct FailedFiberData
{
    Receipt _result{.status = 1u};
    FailedFiberData(
        TState &, Transaction const &, BlockHeader const &, unsigned int)
    {
    }
    Receipt get_receipt() { return _result; }
    inline void operator()() { boost::this_fiber::yield(); }
};

TEST(AllTxnBlockProcessor, execute_empty)
{
    using block_processor_t = AllTxnBlockProcessor<BoostFiberExecution>;
    using fiber_data_t = EmptyFiberData<state_t>;

    fake::State s{};
    static Block b{
        .header = {},
    };

    block_processor_t p{};
    auto const r = p.execute<state_t, fork_t, fiber_data_t>(s, b);
    EXPECT_EQ(r.size(), 0);
}

TEST(AllTxnBlockProcessor, execute_some)
{
    using block_processor_t = AllTxnBlockProcessor<BoostFiberExecution>;
    using fiber_data_t = EmptyFiberData<state_t>;

    fake::State s{};
    static Block b{
        .header = {},
        .transactions = {{}, {}, {}},
    };

    block_processor_t p{};
    auto const r = p.execute<state_t, fork_t, fiber_data_t>(s, b);
    EXPECT_EQ(r.size(), 3);
    EXPECT_EQ(r[0].status, 0u);
    EXPECT_EQ(r[1].status, 0u);
    EXPECT_EQ(r[2].status, 0u);
}

TEST(AllTxnBlockProcessor, execute_some_failed)
{
    using block_processor_t = AllTxnBlockProcessor<BoostFiberExecution>;
    using fiber_data_t = FailedFiberData<state_t>;

    fake::State s{};
    static Block b{
        .header = {},
        .transactions = {{}, {}, {}, {}, {}},
    };

    block_processor_t p{};
    auto const r = p.execute<state_t, fork_t, fiber_data_t>(s, b);
    EXPECT_EQ(r.size(), 5);
    EXPECT_EQ(r[0].status, 1u);
    EXPECT_EQ(r[1].status, 1u);
    EXPECT_EQ(r[2].status, 1u);
    EXPECT_EQ(r[3].status, 1u);
    EXPECT_EQ(r[4].status, 1u);
}

/*
// TODO: Comment back when both BlockProcessor refactor & transfer_balance_dao
refactor are done

TEST(AllTxnBlockProcessor, complete_transfer_and_verify_still_merge_dao)
{
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    db_t db{};

    using fiber_data_t = EmptyFiberData<real_state_t>;

    std::vector<std::pair<address_t, std::optional<Account>>> v{};
    for (auto const addr : dao::child_accounts) {
        Account a{.balance = individual};
        v.emplace_back(std::make_pair(addr, a));
    }
    v.emplace_back(
        std::make_pair(dao::withdraw_account, Account{}.balance = 0u));
    db.commit(state::StateChanges{.account_changes = v});
    state::AccountState accounts{db};
    state::ValueState values{db};
    state::CodeState codes{db};
    real_state_t s{accounts, values, codes, blocks, db};

    Block b{};
    b.header.number = dao::dao_block_number;

    AllTxnBlockProcessor<BoostFiberExecution> bp{};
    [[maybe_unused]] auto const r =
        bp.execute<real_state_t, fork_traits::dao_fork, fiber_data_t>(s, b);

    auto change_set = s.get_new_changeset(0u);

    for (auto const &addr : dao::child_accounts) {
        EXPECT_EQ(intx::be::load<uint256_t>(change_set.get_balance(addr)), 0u);
    }
    EXPECT_EQ(
        intx::be::load<uint256_t>(
            change_set.get_balance(dao::withdraw_account)),
        total);

    // Verify we can still merge changeset
    change_set.set_balance(dao::withdraw_account, 1);
    EXPECT_EQ(
        s.can_merge_changes(change_set),
        real_state_t::MergeStatus::WILL_SUCCEED);
}

*/
