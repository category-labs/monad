#include <monad/core/account.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>
#include <test_resource_data.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <limits>
#include <optional>
#include <utility>

using namespace monad;
using namespace monad::test;

using db_t = TrieDb;

using evm_host_t = EvmcHost<EVMC_SHANGHAI>;

TEST(Evm, create_with_insufficient)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0xf8636377b7a998b51a3cf2bd711b870b3ab0ad56_address};

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt, Account{.balance = 10'000'000'000}}}}},
        Code{},
        BlockHeader{});

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t const v{70'000'000'000'000'000}; // too much
    intx::be::store(m.value.bytes, v);

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    evm_host_t h{call_tracer, EMPTY_TX_CONTEXT, block_hash_buffer, s};
    auto const result = create<EVMC_SHANGHAI>(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_INSUFFICIENT_BALANCE);
}

TEST(Evm, eip684_existing_code)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x36928500bc1dcd7af6a2b4008875cc336b927d57_address};
    static constexpr auto to{
        0xd0e9eb6589febcdb3e681ba6954e881e73b3eef4_address};
    static constexpr auto code_hash{
        0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32};

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{.balance = 10'000'000'000, .nonce = 7}}}},
            {to,
             StateDelta{
                 .account = {std::nullopt, Account{.code_hash = code_hash}}}}},
        Code{},
        BlockHeader{});

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t const v{70'000'000};
    intx::be::store(m.value.bytes, v);

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    evm_host_t h{call_tracer, EMPTY_TX_CONTEXT, block_hash_buffer, s};
    auto const result = create<EVMC_SHANGHAI>(&h, s, m);
    EXPECT_EQ(result.status_code, EVMC_INVALID_INSTRUCTION);
}

TEST(Evm, create_nonce_out_of_range)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto new_addr{
        0x58f3f9ebd5dbdf751f12d747b02d00324837077d_address};

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    evm_host_t h{call_tracer, EMPTY_TX_CONTEXT, block_hash_buffer, s};

    commit_sequential(
        tdb,
        StateDeltas{
            {from,
             StateDelta{
                 .account =
                     {std::nullopt,
                      Account{
                          .balance = 10'000'000'000,
                          .nonce = std::numeric_limits<uint64_t>::max()}}}}},
        Code{},
        BlockHeader{});

    evmc_message m{
        .kind = EVMC_CREATE,
        .gas = 20'000,
        .sender = from,
    };
    uint256_t const v{70'000'000};
    intx::be::store(m.value.bytes, v);

    auto const result = create<EVMC_SHANGHAI>(&h, s, m);

    EXPECT_FALSE(s.account_exists(new_addr));
    EXPECT_EQ(result.status_code, EVMC_ARGUMENT_OUT_OF_RANGE);
}

TEST(Evm, static_precompile_execution)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000004_address};

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    evm_host_t h{call_tracer, EMPTY_TX_CONTEXT, block_hash_buffer, s};

    commit_sequential(
        tdb,
        StateDeltas{
            {code_address,
             StateDelta{.account = {std::nullopt, Account{.nonce = 4}}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 15'000}}}}},
        Code{},
        BlockHeader{});

    static constexpr char data[] = "hello world";
    static constexpr auto data_size = sizeof(data);

    evmc_message const m{
        .kind = EVMC_CALL,
        .gas = 400,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<unsigned char const *>(data),
        .input_size = data_size,
        .value = {0},
        .code_address = code_address};

    auto const result = call<EVMC_SHANGHAI>(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 382);
    ASSERT_EQ(result.output_size, data_size);
    EXPECT_EQ(std::memcmp(result.output_data, m.input_data, data_size), 0);
    EXPECT_NE(result.output_data, m.input_data);
}

TEST(Evm, out_of_gas_static_precompile_execution)
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    BlockState bs{tdb};
    State s{bs, Incarnation{0, 0}};

    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000001_address};

    BlockHashBufferFinalized const block_hash_buffer;
    NoopCallTracer call_tracer;
    evm_host_t h{call_tracer, EMPTY_TX_CONTEXT, block_hash_buffer, s};

    commit_sequential(
        tdb,
        StateDeltas{
            {code_address,
             StateDelta{.account = {std::nullopt, Account{.nonce = 6}}}},
            {from,
             StateDelta{
                 .account = {std::nullopt, Account{.balance = 15'000}}}}},
        Code{},
        BlockHeader{});

    static constexpr char data[] = "hello world";
    static constexpr auto data_size = sizeof(data);

    evmc_message const m{
        .kind = EVMC_CALL,
        .gas = 100,
        .recipient = code_address,
        .sender = from,
        .input_data = reinterpret_cast<unsigned char const *>(data),
        .input_size = data_size,
        .value = {0},
        .code_address = code_address};

    evmc::Result const result = call<EVMC_SHANGHAI>(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_OUT_OF_GAS);
}

TEST(Evm, deploy_contract_code)
{
    static constexpr auto a{0xbebebebebebebebebebebebebebebebebebebebe_address};

    InMemoryMachine machine;
    mpt::Db db{machine};
    db_t tdb{db};
    commit_sequential(
        tdb,
        StateDeltas{{a, StateDelta{.account = {std::nullopt, Account{}}}}},
        Code{},
        BlockHeader{});
    BlockState bs{tdb};

    // Frontier
    {
        uint8_t const code[] = {0xde, 0xad, 0xbe, 0xef};
        // Successfully deploy code
        {
            State s{bs, Incarnation{0, 0}};
            static constexpr int64_t gas = 10'000;
            evmc::Result r{EVMC_SUCCESS, gas, 0, code, sizeof(code)};
            auto const r2 =
                deploy_contract_code<EVMC_FRONTIER>(s, a, std::move(r));
            EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
            EXPECT_EQ(r2.gas_left, gas - 800); // G_codedeposit * size(code)
            EXPECT_EQ(r2.create_address, a);
            EXPECT_EQ(
                s.get_code(a)->executable_code,
                byte_string(code, sizeof(code)));
        }

        // Initilization code succeeds, but deployment of code failed
        {
            State s{bs, Incarnation{0, 1}};
            evmc::Result r{EVMC_SUCCESS, 700, 0, code, sizeof(code)};
            auto const r2 =
                deploy_contract_code<EVMC_FRONTIER>(s, a, std::move(r));
            EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
            EXPECT_EQ(r2.gas_left, 700);
            EXPECT_EQ(r2.create_address, a);
        }
    }

    // Homestead
    {
        uint8_t const code[] = {0xde, 0xad, 0xbe, 0xef};
        // Successfully deploy code
        {
            State s{bs, Incarnation{0, 2}};
            int64_t const gas = 10'000;

            evmc::Result r{EVMC_SUCCESS, gas, 0, code, sizeof(code)};
            auto const r2 =
                deploy_contract_code<EVMC_HOMESTEAD>(s, a, std::move(r));
            EXPECT_EQ(r2.status_code, EVMC_SUCCESS);
            EXPECT_EQ(r2.create_address, a);
            EXPECT_EQ(r2.gas_left,
                      gas - 800); // G_codedeposit * size(code)
            EXPECT_EQ(
                s.get_code(a)->executable_code,
                byte_string(code, sizeof(code)));
        }

        // Fail to deploy code - out of gas (EIP-2)
        {
            State s{bs, Incarnation{0, 3}};
            evmc::Result r{EVMC_SUCCESS, 700, 0, code, sizeof(code)};
            auto const r2 =
                deploy_contract_code<EVMC_HOMESTEAD>(s, a, std::move(r));
            EXPECT_EQ(r2.status_code, EVMC_OUT_OF_GAS);
            EXPECT_EQ(r2.gas_left, 700);
            EXPECT_EQ(r2.create_address, 0x00_address);
        }
    }

    // Spurious Dragon
    {
        uint8_t const ptr[25000]{0x00};
        byte_string code{ptr, 25000};

        State s{bs, Incarnation{0, 4}};

        evmc::Result r{
            EVMC_SUCCESS,
            std::numeric_limits<int64_t>::max(),
            0,
            code.data(),
            code.size()};
        auto const r2 =
            deploy_contract_code<EVMC_SPURIOUS_DRAGON>(s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_OUT_OF_GAS);
        EXPECT_EQ(r2.gas_left, 0);
        EXPECT_EQ(r2.create_address, 0x00_address);
    }

    // London
    {
        byte_string const illegal_code{0xef, 0x60};

        State s{bs, Incarnation{0, 5}};

        evmc::Result r{
            EVMC_SUCCESS, 1'000, 0, illegal_code.data(), illegal_code.size()};
        auto const r2 = deploy_contract_code<EVMC_LONDON>(s, a, std::move(r));
        EXPECT_EQ(r2.status_code, EVMC_CONTRACT_VALIDATION_FAILURE);
        EXPECT_EQ(r2.gas_left, 0);
        EXPECT_EQ(r2.create_address, 0x00_address);
    }
}

/*
// TODO
TEST(Evm, DISABLED_revert_call)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000003_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 15'000});
    s._accounts.emplace(code_address, Account{.nonce = 10});
    fake::Interpreter::_result = evmc::Result{
        evmc_result{.status_code = EVMC_REVERT, .gas_left = 6'000}};

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 12'000,
        .recipient = code_address,
        .sender = from,
        .code_address = code_address};

    auto const result = evm_t::call(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_REVERT);
    EXPECT_TRUE(s._accounts.empty()); // revert was called on the fake
    EXPECT_EQ(result.gas_left, 6'000);
}

// TODO
TEST(Evm, DISABLED_unsuccessful_call)
{
    static constexpr auto from{
        0x5353535353535353535353535353535353535353_address};
    static constexpr auto code_address{
        0x0000000000000000000000000000000000000003_address};
    fake::State::ChangeSet s{};
    evm_host_t h{};
    s._accounts.emplace(from, Account{.balance = 15'000});
    s._accounts.emplace(code_address, Account{.nonce = 10});
    fake::Interpreter::_result = evmc::Result{evmc_result{
        .status_code = EVMC_BAD_JUMP_DESTINATION, .gas_left = 6'000}};

    evmc_message m{
        .kind = EVMC_CALL,
        .gas = 12'000,
        .recipient = code_address,
        .sender = from,
        .code_address = code_address};

    auto const result = evm_t::call(&h, s, m);

    EXPECT_EQ(result.status_code, EVMC_BAD_JUMP_DESTINATION);
    EXPECT_TRUE(s._accounts.empty()); // revert was called on the fake
    EXPECT_EQ(result.gas_left, 6'000);
}
*/
