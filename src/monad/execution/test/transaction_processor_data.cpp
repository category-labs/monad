#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/state2/state.hpp>

#include <monad/test/make_db.hpp>

#include <gtest/gtest.h>

#include <shared_mutex>

using namespace monad;
using namespace monad::execution;

using mutex_t = std::shared_mutex;
using block_cache_t = fake::BlockDb;

using db_t = db::InMemoryTrieDB;
using state_t = state::State<mutex_t, block_cache_t>;
using traits_t = fake::traits::alpha<state_t>;

template <class TTxnProc>
using data_t = TransactionProcessorFiberData<
    mutex_t, TTxnProc, fake::EvmHost<state_t, fake::traits::alpha<state_t>>,
    block_cache_t>;

namespace
{
    block_cache_t block_cache;
}

enum class TestStatus
{
    SUCCESS,
    LATER_NONCE,
    INSUFFICIENT_BALANCE,
    INVALID_GAS_LIMIT,
    BAD_NONCE,
    DEPLOYED_CODE,
};

static TestStatus fake_status{};

template <class TState, class TTraits>
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

    Receipt r_{.status = Receipt::SUCCESS};

    template <class TEvmHost>
    Receipt execute(
        TState &, TEvmHost &, Transaction const &, uint256_t const &,
        address_t const &) const
    {
        return r_;
    }

    Status validate(TState const &, Transaction const &, uint256_t const &)
    {
        return static_cast<Status>(fake_status);
    }
};

using tp_t = fakeTP<state_t, traits_t>;

TEST(TransactionProcessorFiberData, successful)
{
    auto db = test::make_db<db_t>();
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::SUCCESS;

    data_t<tp_t> d{db, bs, t, b, block_cache, 0};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, Receipt::SUCCESS);
    EXPECT_EQ(r.gas_used, 0);
}

TEST(TransactionProcessorFiberData, failed_validation)
{
    auto db = test::make_db<db_t>();
    BlockState<mutex_t> bs;
    state_t s{bs, db, block_cache};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};

    {
        fake_status = TestStatus::INSUFFICIENT_BALANCE;
        data_t<tp_t> d{db, bs, t, b, block_cache, 0};
        d();
        auto const r = d.get_receipt();

        EXPECT_EQ(r.status, Receipt::FAILED);
        EXPECT_EQ(r.gas_used, 15'000);
    }
    {
        fake_status = TestStatus::BAD_NONCE;
        data_t<tp_t> d{db, bs, t, b, block_cache, 0};
        d();
        auto const r = d.get_receipt();

        EXPECT_EQ(r.status, Receipt::FAILED);
        EXPECT_EQ(r.gas_used, 15'000);
    }
    {
        fake_status = TestStatus::INVALID_GAS_LIMIT;
        data_t<tp_t> d{db, bs, t, b, block_cache, 0};
        d();
        auto const r = d.get_receipt();

        EXPECT_EQ(r.status, Receipt::FAILED);
        EXPECT_EQ(r.gas_used, 15'000);
    }
    {
        fake_status = TestStatus::DEPLOYED_CODE;
        data_t<tp_t> d{db, bs, t, b, block_cache, 0};
        d();
        auto const r = d.get_receipt();

        EXPECT_EQ(r.status, Receipt::FAILED);
        EXPECT_EQ(r.gas_used, 15'000);
    }
}
