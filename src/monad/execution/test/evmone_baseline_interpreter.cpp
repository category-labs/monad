#include <monad/core/address.hpp>

#include <monad/db/db.hpp>
#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::execution;

using db_t = db::InMemoryTrieDB;
using mutex_t = std::shared_mutex;
using block_cache_t = execution::fake::BlockDb;

using state_t = state::State<mutex_t, block_cache_t>;

using traits_t = fork_traits::shanghai;

using interpreter_t = EVMOneBaselineInterpreter<state_t, traits_t>;

using evm_host_t = fake::EvmHost<state_t, traits_t>;

TEST(Evm1BaselineInterpreter, execute_empty)
{
    constexpr address_t a{0x5353535353535353535353535353535353535353_address};

    evm_host_t h{};

    evmc_message m{.kind = EVMC_CALL, .gas = 10'000, .code_address = a};

    auto const r = interpreter_t::execute(&h, m, {});

    EXPECT_EQ(r.gas_left, m.gas);
    EXPECT_EQ(r.status_code, EVMC_SUCCESS);
}

TEST(Evm1BaselineInterpreter, execute_simple)
{
    constexpr address_t a{0x5353535353535353535353535353535353535353_address};
    evm_host_t h{};
    byte_string const code = {
        0x60, // PUSH1, 3 gas
        0x64, // 'd'
        0x60, // PUSH1, 3 gas
        0x02, // offset
        0x60, // PUSH1, 3 gas
        0x0b, // length
        0x00}; // STOP

    evmc_message m{.kind = EVMC_CALL, .gas = 10'000, .code_address = a};

    auto const r = interpreter_t::execute(&h, m, code);

    EXPECT_EQ(r.status_code, EVMC_SUCCESS);
    EXPECT_EQ(r.gas_left, m.gas - 9);
}

TEST(Evm1BaselineInterpreter, execute_invalid)
{
    constexpr address_t a{0x5353535353535353535353535353535353535353_address};
    evm_host_t h{};
    byte_string const code = {
        0x60, // PUSH1, 3 gas
        0x68, // 'h'
        0xfe}; // INVALID

    evmc_message m{.kind = EVMC_CALL, .gas = 10'000, .code_address = a};

    auto const r = interpreter_t::execute(&h, m, code);

    EXPECT_EQ(r.status_code, EVMC_INVALID_INSTRUCTION);
    EXPECT_EQ(r.gas_left, 0);
}
