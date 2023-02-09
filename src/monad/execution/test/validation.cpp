#include <monad/config.hpp>
#include <monad/execution/processor.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

TEST(Execution, static_validate_no_sender)
{
    using processor_t = Processor<fake::traits>;
    processor_t p{};
    Transaction const t{};

    EXPECT_DEATH(p.static_validate(t), "from.has_value");
}

TEST(Execution, validate_enough_gas)
{
    using processor_t = Processor<fake::traits>;
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .amount = 1,
        .from = a};

    fake::Accounts accounts{};
    accounts._map[a] = {.balance = 55'939'568'773'815'811};
    fake::traits::_intrinsic_gas = 53'000;

    auto status = p.validate(accounts, t);
    EXPECT_EQ(status, processor_t::Status::INVALID_GAS_LIMIT);
}

TEST(Execution, validate_deployed_code)
{
    using processor_t = Processor<fake::traits>;
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    fake::Accounts accounts{};
    accounts._map[a] = {56'939'568'773'815'811, some_non_null_hash, 24};
    fake::traits::_intrinsic_gas = 27'500;

    Transaction const t{.gas_limit = 27'500, .from = a};

    auto status = p.validate(accounts, t);
    EXPECT_EQ(status, processor_t::Status::DEPLOYED_CODE);
}

TEST(Execution, validate_nonce)
{
    using processor_t = Processor<fake::traits>;
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 25,
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .from = a};

    fake::Accounts accounts{};
    accounts._map[a] = {.balance = 56'939'568'773'815'811, .nonce = 24};
    auto status = p.validate(accounts, t);
    EXPECT_EQ(status, processor_t::Status::BAD_NONCE);
}

TEST(Execution, validate_enough_balance)
{
    using processor_t = Processor<fake::traits>;
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a};

    fake::Accounts accounts{};
    accounts._map[a] = {.balance = 55'939'568'773'815'811};
    fake::traits::_intrinsic_gas = 21'000;

    auto status = p.validate(accounts, t);
    EXPECT_EQ(status, processor_t::Status::INSUFFICIENT_BALANCE);
}

TEST(Execution, successful_validation)
{
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto b{0x5353535353535353535353535353535353535353_address};
    fake::Accounts accounts{};
    accounts._map[a] = {.balance = 56'939'568'773'815'811, .nonce = 25};
    fake::traits::_intrinsic_gas = 21'000;

    static Transaction const t{
        .nonce = 25,
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a};

    using processor_t = Processor<fake::traits>;
    processor_t p{};

    auto status = p.validate(accounts, t);
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
}

