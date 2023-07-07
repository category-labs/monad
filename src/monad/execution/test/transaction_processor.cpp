#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using traits_t = fake::traits::alpha<fake::State::WorkingCopy>;
using processor_t = TransactionProcessor<fake::State::WorkingCopy, traits_t>;

using evm_host_t = fake::EvmHost<
    fake::State::WorkingCopy, traits_t,
    fake::Evm<
        fake::State::WorkingCopy, traits_t,
        fake::static_precompiles::OneHundredGas, fake::Interpreter>>;

TEST(TransactionProcessor, g_star)
{
    fake::State::WorkingCopy s{};
    traits_t::_sd_refund = 10'000;
    traits_t::_max_refund_quotient = 2;

    static Transaction const t{
        .gas_limit = 51'000,
    };

    processor_t p{};

    EXPECT_EQ(p.g_star(s, t, 1'002, 15'000), 26'001);
    EXPECT_EQ(p.g_star(s, t, 1'001, 15'000), 26'000);
    EXPECT_EQ(p.g_star(s, t, 1'000, 15'000), 26'000);
    EXPECT_EQ(p.g_star(s, t, 999, 15'000), 25'999);
}

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
{
    constexpr static auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    fake::State::WorkingCopy s{};
    evm_host_t h{};
    s._accounts[from] = {.balance = 56'000'000'000'000'000, .nonce = 25};
    h._result = {.status_code = EVMC_SUCCESS, .gas_left = 15'000};
    h._receipt = {.status = 1u};
    traits_t::_sd_refund = 24'000;

    static Transaction const t{
        .nonce = 25,
        .gas_price = 53'500,
        .gas_limit = 53'500,
        .from = from,
        .priority_fee = 10'000,
    };

    processor_t p{};

    auto status = p.validate(s, t, 0);
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
    auto result = p.execute(s, h, t, 0u);
    EXPECT_EQ(result.status, 1u);
    EXPECT_EQ(s._accounts[from].balance, uint256_t{55'999'999'807'500'000});
    EXPECT_EQ(s._accounts[from].nonce, 25); // EVMC will inc for creation
}

TEST(
    TransactionProcessor, irrevocable_gas_and_refund_with_base_fee_new_contract)
{
    constexpr static auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    fake::State::WorkingCopy s{};
    evm_host_t h{};

    s._accounts[from] = {.balance = 56'000'000'000'000'000, .nonce = 25};
    h._result = {
        .status_code = EVMC_SUCCESS, .gas_left = 15'000, .gas_refund = 1'000};
    h._receipt = {.status = 1u};
    traits_t::_sd_refund = 24'000;

    static Transaction const t{
        .nonce = 25,
        .gas_price = 75'000'000'000,
        .gas_limit = 90'000,
        .from = from,
        .priority_fee = 100'000'000,
    };

    processor_t p{};

    auto status = p.validate(s, t, 38'000'000'000);
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
    auto result = p.execute(s, h, t, 38'000'000'000);
    EXPECT_EQ(result.status, 1u);
    EXPECT_EQ(s._accounts[from].balance, uint256_t{54'095'000'000'000'000});
    EXPECT_EQ(s._accounts[from].nonce, 25); // EVMC will inc for creation
}
