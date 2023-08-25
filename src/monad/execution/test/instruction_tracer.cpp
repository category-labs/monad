#include <gtest/gtest.h>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/ethereum/genesis.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/evmone_baseline_interpreter.hpp>
#include <monad/execution/instruction_tracer.hpp>
#include <monad/execution/static_precompiles.hpp>
#include <monad/execution/test/fakes.hpp>
#include <monad/execution/transaction_processor.hpp>
#include <monad/state/account_state.hpp>
#include <monad/state/code_state.hpp>
#include <monad/state/state.hpp>
#include <monad/state/state_changes.hpp>
#include <monad/state/value_state.hpp>

#include <nlohmann/json.hpp>

using namespace monad;
using namespace monad::execution;

using in_memory_db_t = monad::db::InMemoryTrieDB;
using state_t = monad::state::State<
    monad::state::AccountState<in_memory_db_t>,
    monad::state::ValueState<in_memory_db_t>,
    monad::state::CodeState<in_memory_db_t>, fake::BlockDb, in_memory_db_t>;
using working_state_t = decltype(std::declval<state_t>().get_new_changeset(0u));

template <typename TFork>
using interpreter_t =
    monad::execution::EVMOneBaselineInterpreter<working_state_t, TFork>;

template <typename TFork>
using transaction_processor_t =
    monad::execution::TransactionProcessor<working_state_t, TFork>;

template <typename TFork>
using static_precompiles_t = monad::execution::StaticPrecompiles<
    working_state_t, TFork, typename TFork::static_precompiles_t>;

template <typename TFork>
using evm_t = monad::execution::Evm<
    working_state_t, TFork, static_precompiles_t<TFork>, interpreter_t<TFork>>;

template <typename TFork>
using host_t = monad::execution::EvmcHost<working_state_t, TFork, evm_t<TFork>>;

std::vector<std::string> split_string_by_newline(std::string const &input)
{
    std::istringstream iss(input);
    std::vector<std::string> lines;

    std::string line;
    while (std::getline(iss, line)) {
        lines.push_back(line);
    }

    return lines;
}

// taken from the add.json in the ethereum test suite
TEST(TransactionTrace, transaction_add)
{
    using namespace evmc::literals;
    fake::BlockDb blocks;
    in_memory_db_t db{};
    monad::state::AccountState accounts{db};
    monad::state::ValueState values{db};
    monad::state::CodeState codes{db};
    monad::state::State s{accounts, values, codes, blocks, db};

    auto change_set = s.get_new_changeset(0u);
    {
        change_set.create_account(
            0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba_address);
        change_set.create_account(
            0x0000000000000000000000000000000000000100_address);
        change_set.set_code(
            0x0000000000000000000000000000000000000100_address,
            evmc::from_hex(
                "7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                "fffffffffff7fffffffffffffffffffffffffffffffffffffffffff"
                "ffffffffffffffffffffff0160005500")
                .value());
        change_set.set_balance(
            0x0000000000000000000000000000000000000100_address,
            0xba1a9ce0ba1a9ce);
        change_set.set_nonce(
            0x0000000000000000000000000000000000000100_address, 0);
        change_set.create_account(
            0x0000000000000000000000000000000000000101_address);
        change_set.set_code(
            0x0000000000000000000000000000000000000101_address,
            evmc::from_hex(
                "60047ffffffffffffffffffffffffffffffffffffffffffffffffff"
                "fffffffffffffff0160005500")
                .value());
        change_set.set_balance(
            0x0000000000000000000000000000000000000101_address,
            0xba1a9ce0ba1a9ce);
        change_set.set_nonce(
            0x0000000000000000000000000000000000000101_address, 0x0);
        change_set.create_account(
            0x0000000000000000000000000000000000000102_address);
        change_set.set_code(
            0x0000000000000000000000000000000000000102_address,
            evmc::from_hex(
                "60017ffffffffffffffffffffffffffffffffffffffffffffffffff"
                "fffffffffffffff0160005500")
                .value());
        change_set.set_balance(
            0x0000000000000000000000000000000000000102_address,
            0xba1a9ce0ba1a9ce);
        change_set.set_nonce(
            0x0000000000000000000000000000000000000102_address, 0x0);
        change_set.create_account(
            0x0000000000000000000000000000000000000103_address);
        change_set.set_code(
            0x0000000000000000000000000000000000000103_address,
            evmc::from_hex("600060000160005500").value());
        change_set.set_balance(
            0x0000000000000000000000000000000000000103_address,
            0xba1a9ce0ba1a9ce);
        change_set.set_nonce(
            0x0000000000000000000000000000000000000103_address, 0x0);
        change_set.create_account(
            0x0000000000000000000000000000000000000104_address);
        change_set.set_code(
            0x0000000000000000000000000000000000000104_address,
            evmc::from_hex(
                "7ffffffffffffffffffffffffffffffffffffffffffffffffffffff"
                "fffffffffff60010160005500")
                .value());
        change_set.set_balance(
            0x0000000000000000000000000000000000000104_address,
            0xba1a9ce0ba1a9ce);
        change_set.set_nonce(
            0x0000000000000000000000000000000000000104_address, 0x0);
        change_set.create_account(
            0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address);
        change_set.set_balance(
            0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address,
            0xba1a9ce0ba1a9ce);
        change_set.set_nonce(
            0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address, 0x0);
        change_set.create_account(
            0xcccccccccccccccccccccccccccccccccccccccc_address);
        change_set.set_code(
            0xcccccccccccccccccccccccccccccccccccccccc_address,
            evmc::from_hex("600060006000600060006004356101000162fffffff100")
                .value());
        change_set.set_balance(
            0xcccccccccccccccccccccccccccccccccccccccc_address,
            0xba1a9ce0ba1a9ce);
        change_set.set_nonce(
            0xcccccccccccccccccccccccccccccccccccccccc_address, 0x0);
    }

    monad::Transaction transaction = {
        .nonce = 0,
        .gas_price = 0xa,
        .gas_limit = 0x4c4b400,
        .amount = 0x01,
        .to = 0xcccccccccccccccccccccccccccccccccccccccc_address,
        .from = 0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address,
        .data = evmc::from_hex(
                    "0x693c6139000000000000000000000000000000000000000000000000"
                    "00000000"
                    "00000000")
                    .value(),
    };

    change_set.access_account(
        0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b_address);
    BlockHeader block_header;
    host_t<fork_traits::berlin> evm_host{block_header, transaction, change_set};
    transaction_processor_t<fork_traits::berlin> transaction_processor;

    auto const receipt = transaction_processor.execute(
        change_set,
        evm_host,
        transaction,
        evm_host.block_header_.base_fee_per_gas.value_or(0));

    auto const geth_trace_lines = split_string_by_newline(
        R"({"pc":0,"op":96,"gas":"0x4c46138","gasCost":"0x3","memSize":0,"stack":[],"depth":1,"refund":0,"opName":"PUSH1"}
{"pc":2,"op":96,"gas":"0x4c46135","gasCost":"0x3","memSize":0,"stack":["0x0"],"depth":1,"refund":0,"opName":"PUSH1"}
{"pc":4,"op":96,"gas":"0x4c46132","gasCost":"0x3","memSize":0,"stack":["0x0","0x0"],"depth":1,"refund":0,"opName":"PUSH1"}
{"pc":6,"op":96,"gas":"0x4c4612f","gasCost":"0x3","memSize":0,"stack":["0x0","0x0","0x0"],"depth":1,"refund":0,"opName":"PUSH1"}
{"pc":8,"op":96,"gas":"0x4c4612c","gasCost":"0x3","memSize":0,"stack":["0x0","0x0","0x0","0x0"],"depth":1,"refund":0,"opName":"PUSH1"}
{"pc":10,"op":96,"gas":"0x4c46129","gasCost":"0x3","memSize":0,"stack":["0x0","0x0","0x0","0x0","0x0"],"depth":1,"refund":0,"opName":"PUSH1"}
{"pc":12,"op":53,"gas":"0x4c46126","gasCost":"0x3","memSize":0,"stack":["0x0","0x0","0x0","0x0","0x0","0x4"],"depth":1,"refund":0,"opName":"CALLDATALOAD"}
{"pc":13,"op":97,"gas":"0x4c46123","gasCost":"0x3","memSize":0,"stack":["0x0","0x0","0x0","0x0","0x0","0x0"],"depth":1,"refund":0,"opName":"PUSH2"}
{"pc":16,"op":1,"gas":"0x4c46120","gasCost":"0x3","memSize":0,"stack":["0x0","0x0","0x0","0x0","0x0","0x0","0x100"],"depth":1,"refund":0,"opName":"ADD"}
{"pc":17,"op":98,"gas":"0x4c4611d","gasCost":"0x3","memSize":0,"stack":["0x0","0x0","0x0","0x0","0x0","0x100"],"depth":1,"refund":0,"opName":"PUSH3"}
{"pc":21,"op":241,"gas":"0x4c4611a","gasCost":"0x1000a27","memSize":0,"stack":["0x0","0x0","0x0","0x0","0x0","0x100","0xffffff"],"depth":1,"refund":0,"opName":"CALL"}
{"pc":0,"op":127,"gas":"0xffffff","gasCost":"0x3","memSize":0,"stack":[],"depth":2,"refund":0,"opName":"PUSH32"}
{"pc":33,"op":127,"gas":"0xfffffc","gasCost":"0x3","memSize":0,"stack":["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"],"depth":2,"refund":0,"opName":"PUSH32"}
{"pc":66,"op":1,"gas":"0xfffff9","gasCost":"0x3","memSize":0,"stack":["0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff","0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"],"depth":2,"refund":0,"opName":"ADD"}
{"pc":67,"op":96,"gas":"0xfffff6","gasCost":"0x3","memSize":0,"stack":["0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"],"depth":2,"refund":0,"opName":"PUSH1"}
{"pc":69,"op":85,"gas":"0xfffff3","gasCost":"0x5654","memSize":0,"stack":["0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe","0x0"],"depth":2,"refund":0,"opName":"SSTORE"}
{"pc":70,"op":0,"gas":"0xffa99f","gasCost":"0x0","memSize":0,"stack":[],"depth":2,"refund":0,"opName":"STOP"}
{"pc":22,"op":0,"gas":"0x4c40092","gasCost":"0x0","memSize":0,"stack":["0x1"],"depth":1,"refund":0,"opName":"STOP"}
{"output":"","gasUsed":"0x60a6"})");

    auto const monad_trace = InstructionTracer::get_trace();
    auto const monad_trace_lines = split_string_by_newline(monad_trace);

    ASSERT_EQ(geth_trace_lines.size(), monad_trace_lines.size());

    for (size_t i = 0; i < geth_trace_lines.size(); i++) {
        // we cannot test for string equality because there might actually be
        // gas differences. so as a jank test for structural equality, we try to
        // merge the two json objects and assert that the size of the merged
        // object is the same
        auto geth_json = nlohmann::json::parse(geth_trace_lines[i]);
        auto monad_json = nlohmann::json::parse(monad_trace_lines[i]);
        auto merged = geth_json;
        merged.update(monad_json);

        EXPECT_EQ(merged.size(), geth_json.size())
            << "at index " << i << std::endl
            << "monad trace: " << monad_trace_lines[i] << std::endl
            << "geth  trace: " << geth_trace_lines[i] << std::endl;
    }

    std::cout << "full monad trace: " << monad_trace << std::endl;
}
