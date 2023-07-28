#include <monad/core/concepts.hpp>

#include <monad/db/block_db.hpp>
#include <monad/db/in_memory_db.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>

#include <monad/execution/test/fakes.hpp>

#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/state_changes.hpp>
#include <monad/state/value_state.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <unordered_map>

using namespace monad;

static constexpr auto from = 0x5353535353535353535353535353535353535353_address;
static constexpr auto to = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto a = 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5_address;
static constexpr auto location =
    0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;
static constexpr auto value1 =
    0x000000000000000000000000000000000000000000000000000000000000004c_bytes32;

using code_db_t = std::unordered_map<address_t, byte_string>;
using account_store_db_t = db::InMemoryDB;

template <class TState, concepts::fork_traits<TState> TTraits>
using traits_templated_static_precompiles_t = execution::StaticPrecompiles<
    TState, TTraits, typename TTraits::static_precompiles_t>;

template <class TState, concepts::fork_traits<TState> TTraits>
using evm_t = execution::Evm<
    TState, TTraits, traits_templated_static_precompiles_t<TState, TTraits>,
    execution::EVMOneBaselineInterpreter<TState, TTraits>>;

template <class TState, concepts::fork_traits<TState> TTraits>
using evm_host_t = execution::EvmcHost<TState, TTraits, evm_t<TState, TTraits>>;

TEST(EvmInterpStateHost, return_existing_storage)
{
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    state::AccountState accounts{db};
    state::ValueState values{db};
    code_db_t code_db{};
    state::CodeState codes{code_db};
    state::State s{accounts, values, codes, blocks, db};

    // Setup db - gas costs referenced here
    // https://www.evm.codes/?fork=byzantium
    byte_string code = {
        0x60, // PUSH1, 3 gas
        0x00, // key
        0x54, // SLOAD, 200 gas (byzantium)
        0x60, // PUSH1, 3 gas
        0x00, // offset
        0x52, // MSTORE, 6 gas
        0x60, // PUSH1, 3 gas
        0x01, // length
        0x60, // PUSH1, 3 gas
        0x1f, // offset
        0xf3}; // RETURN
    code_db.emplace(a, code);
    Account A{};

    db.commit(state::StateChanges{
        .account_changes =
            {{a, A}, {to, Account{}}, {from, Account{.balance = 10'000'000}}},
        .storage_changes = {{to, {{location, value1}}}}});

    BlockHeader const b{}; // Required for the host interface, but not used
    Transaction const t{};
    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 10'000,
        .recipient = to,
        .sender = from,
        .code_address = a};

    // Get new changeset
    auto changeset = s.get_new_changeset(0u);

    using fork_t = monad::fork_traits::byzantium;
    using state_t = decltype(changeset);

    // Prep per transaction processor
    changeset.access_account(to);
    changeset.access_account(from);

    evm_t<state_t, fork_t> e{};
    evm_host_t<state_t, fork_t> h{b, t, changeset};

    auto status = e.call_evm(&h, changeset, m);

    EXPECT_EQ(status.status_code, EVMC_SUCCESS);
    EXPECT_EQ(status.output_size, 1u);
    EXPECT_EQ(*(status.output_data), 0x4c);
    EXPECT_EQ(status.gas_left, 9'782);
}

TEST(EvmInterpStateHost, store_then_return_storage)
{
    db::BlockDb blocks{test_resource::correct_block_data_dir};
    account_store_db_t db{};
    state::AccountState accounts{db};
    state::ValueState values{db};
    code_db_t code_db{};
    state::CodeState codes{code_db};
    state::State s{accounts, values, codes, blocks, db};

    // Setup db - gas costs referenced here
    // https://www.evm.codes/?fork=byzantium
    byte_string code = {
        0x60, // PUSH1, 3 gas
        0x4d,
        0x60, // PUSH1, 3 gas
        0x00,
        0x55, // SSTORE, 20'000
        0x60, // PUSH1, 3 gas
        0x00, // key
        0x54, // SLOAD, 200 gas (byzantium)
        0x60, // PUSH1, 3 gas
        0x00, // offset
        0x52, // MSTORE, 6 gas
        0x60, // PUSH1, 3 gas
        0x01, // length
        0x60, // PUSH1, 3 gas
        0x1f, // offset
        0xf3}; // RETURN
    code_db.emplace(a, code);
    Account A{};

    db.commit(state::StateChanges{
        .account_changes =
            {{a, A}, {to, Account{}}, {from, Account{.balance = 10'000'000}}},
        .storage_changes = {}});

    BlockHeader const b{}; // Required for the host interface, but not used
    Transaction const t{};
    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 20'225,
        .recipient = to,
        .sender = from,
        .code_address = a};

    // Get new changeset
    auto changeset = s.get_new_changeset(0u);

    using fork_t = monad::fork_traits::byzantium;
    using state_t = decltype(changeset);

    // Prep per transaction processor
    changeset.access_account(to);
    changeset.access_account(from);

    evm_t<state_t, fork_t> e{};
    evm_host_t<state_t, fork_t> h{b, t, changeset};

    auto status = e.call_evm(&h, changeset, m);

    EXPECT_EQ(status.status_code, EVMC_SUCCESS);
    EXPECT_EQ(status.output_size, 1u);
    EXPECT_EQ(*(status.output_data), 0x4d);
    EXPECT_EQ(status.gas_left, 1);
}

// TODO
// TEST(EvmInterpStateHost, delegate_call)
// TEST(EvmInterpStateHost, create_new_contract)
// TEST(EvmInterpStateHost, keep_irrevocable_change)
