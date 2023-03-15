#include <monad/execution/block_processor.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/execution_model.hpp>

#include <monad/execution/test/fakes.hpp>

#include <boost/fiber/all.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using state_t = fake::State;

template <class TState>
struct EmptyFiberData
{
    Receipt _result{};
    EmptyFiberData(TState &, Transaction const &, BlockHeader const &, int) {}
    Receipt get_receipt() { return _result; }
    inline void operator()() {}
};

template <class TState>
struct FailedFiberData
{
    Receipt _result{.status = 1u};
    FailedFiberData(TState &, Transaction const &, BlockHeader const &, int) {}
    Receipt get_receipt() { return _result; }
    inline void operator()() { boost::this_fiber::yield(); }
};

TEST(AllTxnBlockProcessor, execute_empty)
{
    using block_processor_t = AllTxnBlockProcessor<BoostFiberExecution>;
    using fiber_data_t = EmptyFiberData<state_t>;

    fake::State s{};
    static Block const b{
        .header = {},
    };

    block_processor_t p{};
    auto const r = p.execute<state_t, fiber_data_t>(s, b);
    EXPECT_EQ(r.size(), 0);
}

TEST(AllTxnBlockProcessor, execute_some)
{
    using block_processor_t = AllTxnBlockProcessor<BoostFiberExecution>;
    using fiber_data_t = EmptyFiberData<state_t>;

    fake::State s{};
    static Block const b{
        .header = {},
        .transactions = {{}, {}, {}},
    };

    block_processor_t p{};
    auto const r = p.execute<state_t, fiber_data_t>(s, b);
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
    static Block const b{
        .header = {},
        .transactions = {{}, {}, {}, {}, {}},
    };

    block_processor_t p{};
    auto const r = p.execute<state_t, fiber_data_t>(s, b);
    EXPECT_EQ(r.size(), 5);
    EXPECT_EQ(r[0].status, 1u);
    EXPECT_EQ(r[1].status, 1u);
    EXPECT_EQ(r[2].status, 1u);
    EXPECT_EQ(r[3].status, 1u);
    EXPECT_EQ(r[4].status, 1u);
}
