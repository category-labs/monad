#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using traits_t = fake::traits::alpha<fake::State::ChangeSet>;
using processor_t = TransactionProcessor<fake::State::ChangeSet, traits_t>;

using evm_host_t = fake::EvmHost<
    fake::State::ChangeSet, traits_t,
    fake::Evm<fake::State::ChangeSet, traits_t, fake::Interpreter>>;

TEST(TransactionProcessor, g_star)
{
    traits_t::_max_refund_quotient = 2;

    static Transaction const t{
        .gas_limit = 51'000,
    };

    processor_t p{};

    EXPECT_EQ(p.g_star(t, 1'002, 15'000), 16'002);
    EXPECT_EQ(p.g_star(t, 1'001, 15'000), 16'001);
    EXPECT_EQ(p.g_star(t, 1'000, 15'000), 16'000);
    EXPECT_EQ(p.g_star(t, 999, 15'000), 15'999);
}

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
{
    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    static constexpr auto bene{
        0x5353535353535353535353535353535353535353_address};

    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts[from] = {.balance = 56'000'000'000'000'000, .nonce = 25};
    h._result = {.status_code = EVMC_SUCCESS, .gas_left = 15'000};
    h._receipt = {.status = 1u};

    static Transaction const t{
        .nonce = 25,
        .gas_price = 10,
        .gas_limit = 55'000,
        .from = from,
    };

    processor_t p{};

    auto status = p.validate(s, t, 10u);
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
    auto result = p.execute(s, h, t, 10u, bene);
    EXPECT_EQ(result.status, 1u);
    EXPECT_EQ(s._accounts[from].balance, uint256_t{55'999'999'999'600'000});
    EXPECT_EQ(s._accounts[from].nonce, 25); // EVMC will inc for creation

    // check if miner gets the right reward
    EXPECT_EQ(s._reward, uint256_t{400'000});
}
