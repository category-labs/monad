#include <monad/execution/config.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/execution/transaction_processor_data.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using state_t = fake::State;
using traits_t = fake::traits<state_t>;

template <class TTxnProc, class TExecution>
using data_t = TransactionProcessorFiberData<
    state_t, traits_t, TTxnProc, fake::Evm, TExecution>;

template <class TState, concepts::fork_traits<TState> TTraits>
struct fakeSuccessfulTP
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

    Receipt _receipt{};
    Status _status{Status::SUCCESS};

    template <class TEvmHost>
    Receipt execute(
        TState &, TEvmHost &, BlockHeader const &, Transaction const &) const
    {
        return _receipt;
    }

    Status validate(TState const &, Transaction const &, uint64_t)
    {
        return _status;
    }
};

TEST(TransactionProcessorFiberData, invoke_successfully_first_time)
{
    fake::State s{._applied_state = true};
    static BlockHeader const b{};
    static Transaction const t{};

    data_t<fakeSuccessfulTP<state_t, traits_t>, BoostFiberExecution> d{
        s, t, b, 0};
    d();
    auto const r = d.get_receipt();

    EXPECT_EQ(r.status, 0u);
}

