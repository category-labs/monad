#include <monad/execution/config.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using state_t = fake::State;
using traits_t = fake::traits::alpha<state_t>;

template <class TTxnProc, class TExecution>
using data_t = TransactionProcessorFiberData<
    state_t, TTxnProc,
    fake::EvmHost<
        fake::State::WorkingCopy, fake::traits::alpha<fake::State::WorkingCopy>,
        fake::Evm<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>,
            fake::static_precompiles::OneHundredGas, fake::Interpreter>>,
    TExecution>;

enum class TestStatus
{
    SUCCESS,
    LATER_NONCE,
    INSUFFICIENT_BALANCE,
    INVALID_GAS_LIMIT,
    BAD_NONCE,
    DEPLOYED_CODE,
};

TestStatus fake_status{};

template <class TState, concepts::fork_traits<TState> TTraits>
struct fakeGlobalStatusTP
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

    template <class TEvmHost>
    Receipt execute(
        TState &, TEvmHost &, BlockHeader const &, Transaction const &) const
    {
        return {};
    }

    Status validate(TState const &, Transaction const &, uint64_t)
    {
        return static_cast<Status>(fake_status);
    }
};

struct fakeSuccessAfterYieldEM
{
    using fiber_t = boost::fibers::fiber;
    static inline void yield()
    {
        fake_status = TestStatus::SUCCESS;
        boost::this_fiber::yield();
    }
};

TEST(
    TransactionProcessorFiberData,
    validation_insufficient_balance_current_txn_id)
{
    fake::State s{
        ._current_txn = 10,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::INSUFFICIENT_BALANCE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        BoostFiberExecution>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}

TEST(TransactionProcessorFiberData, validation_insufficient_balance_optimistic)
{
    fake::State s{
        ._current_txn = 1,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::INSUFFICIENT_BALANCE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        fakeSuccessAfterYieldEM>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}

TEST(TransactionProcessorFiberData, validation_later_nonce_current_txn_id)
{
    fake::State s{
        ._current_txn = 10,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{};
    fake_status = TestStatus::LATER_NONCE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        BoostFiberExecution>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    // This should fail, but currently does not
    EXPECT_EQ(r.status, 1u);
}

TEST(TransactionProcessorFiberData, validation_later_nonce_optimistic)
{
    fake::State s{
        ._current_txn = 1,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{};
    fake_status = TestStatus::LATER_NONCE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        fakeSuccessAfterYieldEM>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 0u);
}

TEST(TransactionProcessorFiberData, validation_invalid_gas_limit_current_txn_id)
{
    fake::State s{
        ._current_txn = 10,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::INVALID_GAS_LIMIT;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        BoostFiberExecution>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}

TEST(TransactionProcessorFiberData, validation_invalid_gas_limit_optimistic)
{
    fake::State s{
        ._current_txn = 1,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::INVALID_GAS_LIMIT;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        fakeSuccessAfterYieldEM>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}

TEST(TransactionProcessorFiberData, validation_bad_nonce_current_txn_id)
{
    fake::State s{
        ._current_txn = 10,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::BAD_NONCE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        BoostFiberExecution>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}

TEST(TransactionProcessorFiberData, validation_bad_nonce_optimistic)
{
    fake::State s{
        ._current_txn = 1,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::BAD_NONCE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        fakeSuccessAfterYieldEM>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}

TEST(TransactionProcessorFiberData, validation_deployed_code_current_txn_id)
{
    fake::State s{
        ._current_txn = 10,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::DEPLOYED_CODE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        BoostFiberExecution>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}

TEST(TransactionProcessorFiberData, validation_deployed_code_optimistic)
{
    fake::State s{
        ._current_txn = 1,
        ._merge_status = fake::State::MergeStatus::WILL_SUCCEED};
    static BlockHeader const b{};
    static Transaction t{.gas_limit = 15'000};
    fake_status = TestStatus::DEPLOYED_CODE;

    data_t<
        fakeGlobalStatusTP<
            fake::State::WorkingCopy,
            fake::traits::alpha<fake::State::WorkingCopy>>,
        fakeSuccessAfterYieldEM>
        d{s, t, b, 10};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 1u);
    EXPECT_EQ(r.gas_used, 15'000);
}
