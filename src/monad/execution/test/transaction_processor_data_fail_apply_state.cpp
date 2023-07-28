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
        fake::State::ChangeSet, fake::traits::alpha<fake::State::ChangeSet>,
        fake::Evm<
            fake::State::ChangeSet,
            fake::traits::alpha<fake::State::ChangeSet>,
            fake::static_precompiles::OneHundredGas, fake::Interpreter>>,
    TExecution>;

state_t global_state{};

template <class TState, concepts::fork_traits<TState> TTraits>
struct fakeEmptyTP
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
        TState &, TEvmHost &, Transaction const &, uint64_t) const
    {
        return {};
    }

    Status validate(TState const &, Transaction const &, uint64_t)
    {
        return {};
    }
};

struct fakeApplyStateAfterYieldEM
{
    using fiber_t = boost::fibers::fiber;
    static inline void yield()
    {
        global_state._merge_status = fake::State::MergeStatus::WILL_SUCCEED;
        boost::this_fiber::yield();
    }
};

TEST(TransactionProcessorFiberData, fail_apply_state_first_time)
{
    static BlockHeader const b{};
    static Transaction t{};
    global_state._merge_status = fake::State::MergeStatus::COLLISION_DETECTED;

    data_t<
        fakeEmptyTP<
            fake::State::ChangeSet,
            fake::traits::alpha<fake::State::ChangeSet>>,
        fakeApplyStateAfterYieldEM>
        d{global_state, t, b, 0};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 0u);
}
