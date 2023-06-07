#include <monad/execution/config.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/static_precompiles.hpp>

#include <monad/execution/test/fakes.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace execution;

using alpha_traits_t = fake::traits::alpha<fake::State>;
using beta_traits_t = fake::traits::beta<fake::State>;

template <concepts::fork_traits<fake::State> TTraits>
using traits_templated_static_precompiles_t = StaticPrecompiles<
    fake::State, TTraits, typename TTraits::static_precompiles_t>;

using alpha_static_precompiles_t =
    traits_templated_static_precompiles_t<alpha_traits_t>;
using beta_static_precompiles_t =
    traits_templated_static_precompiles_t<beta_traits_t>;

TEST(StaticPrecompiles, execution_echo)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000001_address};
    auto exec_func =
        alpha_static_precompiles_t::static_precompile_exec_func(code_address);

    const auto data = "hello world";
    const auto data_size = 11u;

    evmc_message m{
        .gas = 400,
        .input_data = reinterpret_cast<const unsigned char *>(data),
        .input_size = data_size};
    auto const result = exec_func.transform(
        [&m](auto exec_func) { return evmc::Result{exec_func(m)}; });

    EXPECT_EQ(result.has_value(), true);
    EXPECT_EQ(result->status_code, EVMC_SUCCESS);
    EXPECT_EQ(result->gas_left, 290);
    EXPECT_EQ(result->output_size, data_size);
    EXPECT_EQ(std::memcmp(result->output_data, m.input_data, data_size), 0);
    EXPECT_NE(result->output_data, m.input_data);
}

TEST(StaticPrecompiles, beta_traits_execution_echo)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000001_address};
    auto exec_func =
        beta_static_precompiles_t::static_precompile_exec_func(code_address);

    const auto data = "hello world";
    const auto data_size = 11u;

    evmc_message m{
        .gas = 400,
        .input_data = reinterpret_cast<const unsigned char *>(data),
        .input_size = data_size};
    auto const result = exec_func.transform(
        [&m](auto exec_func) { return evmc::Result{exec_func(m)}; });

    EXPECT_EQ(result.has_value(), true);
    EXPECT_EQ(result->status_code, EVMC_SUCCESS);
    EXPECT_EQ(result->gas_left, 235);
    EXPECT_EQ(result->output_size, data_size);
    EXPECT_EQ(std::memcmp(result->output_data, m.input_data, data_size), 0);
    EXPECT_NE(result->output_data, m.input_data);
}

TEST(StaticPrecompiles, out_of_gas_execution_echo)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000001_address};
    auto exec_func =
        beta_static_precompiles_t::static_precompile_exec_func(code_address);

    const auto data = "hello world";
    const auto data_size = 11u;

    evmc_message m{
        .gas = 100,
        .input_data = reinterpret_cast<const unsigned char *>(data),
        .input_size = data_size};
    auto const result =
        exec_func.transform([&m](auto exec_func) { return exec_func(m); });

    EXPECT_EQ(result.has_value(), true);
    EXPECT_EQ(result->status_code, EVMC_OUT_OF_GAS);
}

TEST(StaticPrecompiles, execution_one_hundred_gas)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000002_address};
    auto exec_func =
        beta_static_precompiles_t::static_precompile_exec_func(code_address);

    evmc_message m{.gas = 400};
    auto const result =
        exec_func.transform([&m](auto exec_func) { return exec_func(m); });

    EXPECT_EQ(result.has_value(), true);
    EXPECT_EQ(result->status_code, EVMC_SUCCESS);
    EXPECT_EQ(result->output_size, 0u);
}

TEST(StaticPrecompiles, out_of_gas_execution_one_hundred_gas)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000002_address};
    auto exec_func =
        beta_static_precompiles_t::static_precompile_exec_func(code_address);

    const auto data = "hello world";
    const auto data_size = 11u;

    evmc_message m{
        .gas = 99,
        .input_data = reinterpret_cast<const unsigned char *>(data),
        .input_size = data_size};
    auto const result =
        exec_func.transform([&m](auto exec_func) { return exec_func(m); });

    EXPECT_EQ(result.has_value(), true);
    EXPECT_EQ(result->status_code, EVMC_OUT_OF_GAS);
}

TEST(StaticPrecompiles, zero_address)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000000_address};
    auto exec_func =
        beta_static_precompiles_t::static_precompile_exec_func(code_address);

    EXPECT_EQ(exec_func.has_value(), false);
}

TEST(StaticPrecompiles, non_static_precompile_min)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000003_address};
    auto exec_func =
        beta_static_precompiles_t::static_precompile_exec_func(code_address);

    EXPECT_EQ(exec_func.has_value(), false);
}

TEST(StaticPrecompiles, non_static_precompile_random_bit)
{
    constexpr static auto code_address{
        0x1000000000000000000000000000000000000001_address};
    auto exec_func =
        beta_static_precompiles_t::static_precompile_exec_func(code_address);

    EXPECT_EQ(exec_func.has_value(), false);
}

TEST(StaticPrecompiles, non_static_precompile_expansion)
{
    constexpr static auto code_address{
        0x0000000000000000000000000000000000000002_address};
    auto exec_func =
        alpha_static_precompiles_t::static_precompile_exec_func(code_address);

    EXPECT_EQ(exec_func.has_value(), false);
}
