#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/block_processor.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

#include <monad/state2/state.hpp>
#include <monad/test/make_db.hpp>

#include <test_resource_data.h>

#include <boost/fiber/all.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};

namespace
{
    using block_cache_t = fake::BlockDb;
    using mutex_t = std::shared_mutex;
    using db_t = db::InMemoryTrieDB;
    using state_t = state::State<mutex_t, block_cache_t>;
    using fork_t = fake::traits::alpha<state_t>;
    using evm_t = fake::EvmHost<
        state_t, fake::traits::alpha<state_t>,
        fake::Evm<state_t, fork_t, fake::Interpreter>>;

    block_cache_t block_cache;
    constexpr auto individual = 100u;
    constexpr auto total = individual * 116u;

    enum class ValStatus
    {
        SUCCESS,
        LATER_NONCE,
        INSUFFICIENT_BALANCE,
        INVALID_GAS_LIMIT,
        BAD_NONCE,
        DEPLOYED_CODE,
    };

    static ValStatus fake_validation{};

    template <class TState, concepts::fork_traits<TState> TTraits>
    struct fakeTP
    {
        enum class Status
        {
            SUCCESS,
            LATER_NONCE,
            INSUFFICIENT_BALANCE,
            INVALID_GAS_LIMIT,
            BAD_NONCE,
            DEPLOYED_CODE,
        };

        Receipt r_{.status = Receipt::SUCCESS, .gas_used = 1000u};

        template <class TEvmHost>
        Receipt execute(
            TState &, TEvmHost &, Transaction const &, uint64_t,
            address_t const &) const
        {
            return r_;
        }

        Status validate(TState const &, Transaction const &, uint64_t)
        {
            return static_cast<Status>(fake_validation);
        }
    };

    using tp_t = fakeTP<state_t, fork_t>;
    using fiber_data_t =
        TransactionProcessorFiberData<mutex_t, tp_t, evm_t, block_cache_t>;
    using block_processor_t = AllTxnBlockProcessor;
}

TEST(AllTxnBlockProcessor, execute_empty_block)
{
    auto db = test::make_db<db_t>();

    static Block b{
        .header = {},
    };

    block_processor_t p{};
    auto const r = p.execute<mutex_t, fork_t, fiber_data_t, block_cache_t>(
        b, db, block_cache);
    EXPECT_EQ(r.size(), 0);
}

TEST(AllTxnBlockProcessor, execute_some)
{
    auto db = test::make_db<db_t>();
    fake_validation = ValStatus::SUCCESS;

    static Block b{
        .header = {},
        .transactions = {{}},
    };

    block_processor_t p{};
    auto const r = p.execute<mutex_t, fork_t, fiber_data_t, block_cache_t>(
        b, db, block_cache);

    EXPECT_EQ(r.size(), 1);
    EXPECT_EQ(r[0].status, Receipt::Status::SUCCESS);
}

TEST(AllTxnBlockProcessor, execute_some_failed)
{
    auto db = test::make_db<db_t>();
    fake_validation = ValStatus::BAD_NONCE;

    static Block b{
        .header = {},
        .transactions = {{}, {}, {}, {}, {}},
    };

    block_processor_t p{};
    auto const r = p.execute<mutex_t, fork_t, fiber_data_t, block_cache_t>(
        b, db, block_cache);
    EXPECT_EQ(r.size(), 5);
    EXPECT_EQ(r[0].status, Receipt::Status::FAILED);
    EXPECT_EQ(r[1].status, Receipt::Status::FAILED);
    EXPECT_EQ(r[2].status, Receipt::Status::FAILED);
    EXPECT_EQ(r[3].status, Receipt::Status::FAILED);
    EXPECT_EQ(r[4].status, Receipt::Status::FAILED);
}

TEST(AllTxnBlockProcessor, dao_reversal)
{
    auto db = test::make_db<db_t>();

    std::vector<std::pair<address_t, std::optional<Account>>> v{};
    for (auto const addr : dao::child_accounts) {
        Account a{.balance = individual};
        v.emplace_back(std::make_pair(addr, a));
    }
    v.emplace_back(
        std::make_pair(dao::withdraw_account, Account{}.balance = 0u));
    db.commit(state::StateChanges{.account_changes = v});

    Block b{};
    b.header.number = dao::dao_block_number;

    block_processor_t bp{};
    auto const r =
        bp.execute<mutex_t, fork_traits::dao_fork, fiber_data_t, block_cache_t>(
            b, db, block_cache);

    for (auto const &addr : dao::child_accounts) {
        auto account = db.read_account(addr);
        ASSERT_TRUE(account);
        EXPECT_EQ(account->balance, 0u);
    }

    auto dao_account = db.read_account(dao::withdraw_account);
    ASSERT_TRUE(dao_account);
    EXPECT_EQ(dao_account->balance, total);
}

TEST(AllTxnBlockProcessor, apply_block_award_no_txn)
{
    auto db = test::make_db<db_t>();
    fake_validation = ValStatus::SUCCESS;

    static Block b{
        .header = {.beneficiary = a},
        .transactions = {},
    };

    block_processor_t p{};
    auto const r =
        p.execute<mutex_t, fork_traits::frontier, fiber_data_t, block_cache_t>(
            b, db, block_cache);

    EXPECT_TRUE(db.read_account(a).has_value());
    EXPECT_EQ(db.read_account(a).value().balance, 5'000'000'000'000'000'000);
}

TEST(AllTxnBlockProcessor, apply_block_award_2_txns)
{
    auto db = test::make_db<db_t>();
    fake_validation = ValStatus::SUCCESS;

    static Block b{
        .header = {.beneficiary = a},
        .transactions =
            {Transaction{.gas_price = 10}, Transaction{.gas_price = 10}},
    };

    block_processor_t p{};
    auto const r =
        p.execute<mutex_t, fork_traits::frontier, fiber_data_t, block_cache_t>(
            b, db, block_cache);

    EXPECT_TRUE(db.read_account(a).has_value());
    EXPECT_EQ(
        db.read_account(a).value().balance,
        5'000'000'000'000'000'000 + 2 * 1'000 * 10);
}
