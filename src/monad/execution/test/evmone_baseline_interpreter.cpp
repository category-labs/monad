#include <monad/core/address.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>

#include <monad/execution/test/fakes.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using interpreter_t =
    EVMOneBaselineInterpreter<fake::State, fake::traits::alpha<fake::State>>;

TEST(Evm1BaselineInterpreter, execute_empty)
{
    constexpr address_t a{0x5353535353535353535353535353535353535353_address};
    fake::State s{};
    fake::EvmHost h{};
    s._code.emplace(a, byte_string{});

    evmc_message m{.kind = EVMC_CALL, .gas = 10'000, .code_address = a};

    auto const r = interpreter_t::execute(&h, s, m);

    EXPECT_EQ(r.gas_left, m.gas);
    EXPECT_EQ(r.status_code, EVMC_SUCCESS);
}

TEST(Evm1BaselineInterpreter, execute_simple)
{
    constexpr address_t a{0x5353535353535353535353535353535353535353_address};
    fake::State s{};
    fake::EvmHost h{};
    byte_string code = {
        0x60, // PUSH1, 3 gas
        0x64, // 'd'
        0x60, // PUSH1, 3 gas
        0x02, // offset
        0x60, // PUSH1, 3 gas
        0x0b, // length
        0x00}; // STOP
    s._code.emplace(a, code);

    evmc_message m{.kind = EVMC_CALL, .gas = 10'000, .code_address = a};

    auto const r = interpreter_t::execute(&h, s, m);

    EXPECT_EQ(r.status_code, EVMC_SUCCESS);
    EXPECT_EQ(r.gas_left, m.gas - 9);
}

TEST(Evm1BaselineInterpreter, execute_invalid)
{
    constexpr address_t a{0x5353535353535353535353535353535353535353_address};
    fake::State s{};
    fake::EvmHost h{};
    byte_string code = {
        0x60, // PUSH1, 3 gas
        0x68, // 'h'
        0xfe}; // INVALID
    s._code.emplace(a, code);

    evmc_message m{.kind = EVMC_CALL, .gas = 10'000, .code_address = a};

    auto const r = interpreter_t::execute(&h, s, m);

    EXPECT_EQ(r.status_code, EVMC_INVALID_INSTRUCTION);
    EXPECT_EQ(r.gas_left, 0);
}
