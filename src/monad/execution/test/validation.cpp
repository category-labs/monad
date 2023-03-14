#include <monad/config.hpp>
#include <monad/execution/transaction_processor.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using traits_t = fake::traits<fake::State>;
using processor_t = TransactionProcessor<fake::State, traits_t>;

TEST(Execution, static_validate_no_sender)
{
    processor_t p{};
    Transaction const t{};

    EXPECT_DEATH(p.static_validate(t), "from.has_value");
}

TEST(Execution, validate_enough_gas)
{
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500, // no .to, under the creation amount
        .amount = 1,
        .from = a};

    fake::State state{};
    state._map[a] = {.balance = 55'939'568'773'815'811};
    traits_t::_intrinsic_gas = 53'000;

    auto status = p.validate(state, t, 0);
    EXPECT_EQ(status, processor_t::Status::INVALID_GAS_LIMIT);
}

TEST(Execution, validate_deployed_code)
{
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto some_non_null_hash{
        0x0000000000000000000000000000000000000000000000000000000000000003_bytes32};
    fake::State state{};
    state._map[a] = {56'939'568'773'815'811, some_non_null_hash, 24};
    traits_t::_intrinsic_gas = 27'500;

    static Transaction const t{.gas_limit = 27'500, .from = a};

    auto status = p.validate(state, t, 0);
    EXPECT_EQ(status, processor_t::Status::DEPLOYED_CODE);
}

TEST(Execution, validate_nonce)
{
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 23,
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .from = a};

    fake::State state{};
    state._map[a] = {.balance = 56'939'568'773'815'811, .nonce = 24};
    auto status = p.validate(state, t, 0);
    EXPECT_EQ(status, processor_t::Status::BAD_NONCE);
}

TEST(Execution, validate_nonce_optimistically)
{
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    static Transaction const t{
        .nonce = 25,
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .from = a};

    fake::State state{};
    state._map[a] = {.balance = 56'939'568'773'815'811, .nonce = 24};
    auto status = p.validate(state, t, 0);
    EXPECT_EQ(status, processor_t::Status::LATER_NONCE);
}

TEST(Execution, validate_enough_balance)
{
    processor_t p{};
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto b{0x5353535353535353535353535353535353535353_address};

    static Transaction const t{
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a,
        .priority_fee = 100'000'000,
    };

    fake::State state{};
    state._map[a] = {.balance = 55'939'568'773'815'811};
    traits_t::_intrinsic_gas = 21'000;

    auto status = p.validate(state, t, 0);
    EXPECT_EQ(status, processor_t::Status::INSUFFICIENT_BALANCE);
}

TEST(Execution, successful_validation)
{
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto b{0x5353535353535353535353535353535353535353_address};
    fake::State state{};
    state._map[a] = {.balance = 56'939'568'773'815'811, .nonce = 25};
    traits_t::_intrinsic_gas = 21'000;

    static Transaction const t{
        .nonce = 25,
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a};

    processor_t p{};

    auto status = p.validate(state, t, 0);
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
}

TEST(Execution, insufficient_balance_higher_base_fee)
{
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto b{0x5353535353535353535353535353535353535353_address};
    fake::State state{};
    state._map[a] = {.balance = 56'939'568'773'815'811, .nonce = 25};
    traits_t::_intrinsic_gas = 21'000;

    static Transaction const t{
        .nonce = 25,
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 55'939'568'773'815'811,
        .to = b,
        .from = a,
        .priority_fee = 100'000'000};

    processor_t p{};

    auto status = p.validate(state, t, 37'000'000'000);
    EXPECT_EQ(status, processor_t::Status::INSUFFICIENT_BALANCE);
}

TEST(Execution, successful_validation_higher_base_fee)
{
    constexpr static auto a{0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};
    constexpr static auto b{0x5353535353535353535353535353535353535353_address};
    fake::State state{};
    state._map[a] = {.balance = 50'000'000'000'000'000, .nonce = 25};
    traits_t::_intrinsic_gas = 21'000;

    static Transaction const t{
        .nonce = 25,
        .gas_price = 29'443'849'433,
        .gas_limit = 27'500,
        .amount = 48'979'750'000'000'000,
        .to = b,
        .from = a,
        .priority_fee = 100'000'000};

    processor_t p{};

    auto status = p.validate(state, t, 37'000'000'000);
    EXPECT_EQ(status, processor_t::Status::SUCCESS);
}
