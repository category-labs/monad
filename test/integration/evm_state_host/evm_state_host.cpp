#include <monad/config.hpp>

#include <monad/db/in_memory_trie_db.hpp>

#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>

#include <monad/state2/block_state.hpp>
#include <monad/state2/block_state_ops.hpp>
#include <monad/state2/state.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <iostream>
#include <unordered_map>

using namespace monad;

static constexpr auto from = 0x5353535353535353535353535353535353535353_address;
static constexpr auto to = 0xbebebebebebebebebebebebebebebebebebebebe_address;
static constexpr auto location =
    0x0000000000000000000000000000000000000000000000000000000000000000_bytes32;
static constexpr auto value1 =
    0x000000000000000000000000000000000000000000000000000000000000004c_bytes32;
static constexpr auto code_hash =
    0x00000000000000000000000000000000000000000000000000000000cccccccc_bytes32;

using account_store_db_t = db::InMemoryTrieDB;

template <class TState, class TTraits>
using evm_t = Evm<TState, TTraits>;

TEST(EvmInterpStateHost, return_existing_storage)
{
    account_store_db_t db{};
    BlockState bs;

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
    Account A{.code_hash = code_hash};

    db.commit(
        StateDeltas{
            {to,
             StateDelta{
                 .account = {std::nullopt, A},
                 .storage = {{location, {bytes32_t{}, value1}}}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000'000}}}}},
        Code{{code_hash, code}});

    BlockHeader const b{}; // Required for the host interface, but not used
    Transaction const t{};
    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 10'000,
        .recipient = to,
        .sender = from,
        .code_address = to};

    State s{bs, db};

    using fork_t = monad::fork_traits::byzantium;
    using state_t = decltype(s);

    // Prep per transaction processor
    s.access_account(to);
    s.access_account(from);

    evm_t<state_t, fork_t> e{};
    BlockHashBuffer block_hash_buffer;
    EvmcHost<fork_t> h{block_hash_buffer, b, t, s};

    auto status = e.call_evm(&h, s, m);

    EXPECT_EQ(status.status_code, EVMC_SUCCESS);
    EXPECT_EQ(status.output_size, 1u);
    EXPECT_EQ(*(status.output_data), 0x4c);
    EXPECT_EQ(status.gas_left, 9'782);
}

TEST(EvmInterpStateHost, store_then_return_storage)
{
    account_store_db_t db{};
    BlockState bs;

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
    Account A{.code_hash = code_hash};

    db.commit(
        StateDeltas{
            {to, StateDelta{.account = {std::nullopt, A}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 10'000'000}}}}},
        Code{{code_hash, code}});

    BlockHeader const b{}; // Required for the host interface, but not used
    Transaction const t{};
    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 20'225,
        .recipient = to,
        .sender = from,
        .code_address = to};

    State s{bs, db};

    using fork_t = monad::fork_traits::byzantium;
    using state_t = decltype(s);

    // Prep per transaction processor
    s.access_account(to);
    s.access_account(from);

    evm_t<state_t, fork_t> e{};
    BlockHashBuffer block_hash_buffer;
    EvmcHost<fork_t> h{block_hash_buffer, b, t, s};

    auto status = e.call_evm(&h, s, m);

    EXPECT_EQ(status.status_code, EVMC_SUCCESS);
    EXPECT_EQ(status.output_size, 1u);
    EXPECT_EQ(*(status.output_data), 0x4d);
    EXPECT_EQ(status.gas_left, 1);
}

// TODO
// TEST(EvmInterpStateHost, delegate_call)
// TEST(EvmInterpStateHost, create_new_contract)
// TEST(EvmInterpStateHost, keep_irrevocable_change)
