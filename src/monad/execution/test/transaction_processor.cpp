#include <monad/execution/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using traits_t = fake::traits::alpha<fake::State>;
using processor_t = TransactionProcessor<fake::State, traits_t>;

TEST(TransactionProcessor, g_star)
{
    fake::State s{};
    s._refund = 15'000;
    traits_t::_sd_refund = 10'000;
    traits_t::_max_refund_quotient = 2;

    static Transaction const t{
        .gas_limit = 51'000,
    };

    processor_t p{};

    EXPECT_EQ(p.g_star(s, t, 1'002), 26'001);
    EXPECT_EQ(p.g_star(s, t, 1'001), 26'000);
    EXPECT_EQ(p.g_star(s, t, 1'000), 26'000);
    EXPECT_EQ(p.g_star(s, t, 999), 25'999);
}

TEST(TransactionProcessor, irrevocable_gas_and_refund_new_contract)
{
    constexpr static auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto bene{
        0x5353535353535353535353535353535353535353_address};
    fake::State s{};
    fake::EvmHost e{};
    s._map[from] = {.balance = 56'000'000'000'000'000, .nonce = 25};
    s._map[bene] = {.balance = 0, .nonce = 0};
    s._refund = 1'000;
    e._result = {.status_code = EVMC_SUCCESS, .gas_left = 15'000};
    e._receipt = {.status = 1u};
    traits_t::_sd_refund = 24'000;

    static BlockHeader const b{.beneficiary = bene};
    static Transaction const t{
        .nonce = 25,
        .gas_price = 53'500,
        .gas_limit = 53'500,
        .from = from,
        .priority_fee = 10'000,
    };

    processor_t p{};

    auto status = p.validate(s, t, b.base_fee_per_gas.value_or(0));
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
    auto result = p.execute(s, e, b, t);
    EXPECT_EQ(result.status, 1u);
    EXPECT_EQ(s._map[from].balance, uint256_t{55'999'999'807'500'000});
    EXPECT_EQ(s._map[from].nonce, 25); // EVMC will inc for creation
    EXPECT_EQ(s._map[bene].balance, 192'500'000);
    EXPECT_EQ(s._map[bene].nonce, 0);
}

TEST(
    TransactionProcessor, irrevocable_gas_and_refund_with_base_fee_new_contract)
{
    constexpr static auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto bene{
        0x5353535353535353535353535353535353535353_address};
    fake::State s{};
    fake::EvmHost e{};
    s._map[from] = {.balance = 56'000'000'000'000'000, .nonce = 25};
    s._map[bene] = {.balance = 0, .nonce = 0};
    s._refund = 1'000;
    e._result = {.status_code = EVMC_SUCCESS, .gas_left = 15'000};
    e._receipt = {.status = 1u};
    traits_t::_sd_refund = 24'000;

    static BlockHeader const b{
        .beneficiary = bene, .base_fee_per_gas = 38'000'000'000};
    static Transaction const t{
        .nonce = 25,
        .gas_price = 75'000'000'000,
        .gas_limit = 90'000,
        .from = from,
        .priority_fee = 100'000'000,
    };

    processor_t p{};

    auto status = p.validate(s, t, b.base_fee_per_gas.value());
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
    auto result = p.execute(s, e, b, t);
    EXPECT_EQ(result.status, 1u);
    EXPECT_EQ(s._map[from].balance, uint256_t{54'095'000'000'000'000});
    EXPECT_EQ(s._map[from].nonce, 25); // EVMC will inc for creation
    EXPECT_EQ(s._map[bene].balance, 1'905'000'000'000'000);
    EXPECT_EQ(s._map[bene].nonce, 0);
}
