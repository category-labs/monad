// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>

#include <test_resource_data.h>

#include <test/vm/utils/test_block_hash_buffer.hpp>
#include <test/vm/utils/test_host.hpp>
#include <test/vm/vm/test_vm.hpp>

#include "benchmarktest.hpp"

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <intx/intx.hpp>

#include <benchmark/benchmark.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <format>
#include <fstream>
#include <ios>
#include <iterator>
#include <memory>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace fs = std::filesystem;

namespace json = nlohmann;

using namespace monad::test_resource;

using enum BlockchainTestVM::Implementation;

using namespace monad;
using namespace monad::test;

using monad::vm::test::TestMemory;

struct free_message
{
    static void operator()(evmc_message *msg) noexcept
    {
        if (msg) {
            delete[] msg->input_data;
            delete msg;
        }
    }
};

using msg_ptr = std::unique_ptr<evmc_message, free_message>;

struct benchmark_case
{
    std::string name;
    msg_ptr msg;
    std::vector<std::uint8_t> code;
};

namespace
{
    auto vm_performance_dir = monad::test_resource::ethereum_tests_dir /
                              "BlockchainTests" / "GeneralStateTests" /
                              "VMTests" / "vmPerformance";

    auto make_benchmark(
        TestMemory &test_memory, std::string const &name,
        std::span<std::uint8_t const> code, std::span<std::uint8_t const> input)
    {
        std::vector<std::uint8_t> code_buffer(code.begin(), code.end());

        auto *input_buffer = new std::uint8_t[input.size()];
        std::copy(input.begin(), input.end(), input_buffer);

        auto msg = msg_ptr(new evmc_message{
            .kind = EVMC_CALL,
            .flags = 0,
            .depth = 0,
            .gas = 150'000'000,
            .recipient = {},
            .sender = {},
            .input_data = input_buffer,
            .input_size = input.size(),
            .value = {},
            .create2_salt = {},
            .code_address = {},
            .memory_handle = test_memory.data,
            .memory = test_memory.data,
            .memory_capacity = TestMemory::capacity,
        });

        return benchmark_case{name, std::move(msg), std::move(code_buffer)};
    }

    std::vector<std::uint8_t> read_file(fs::path const &path)
    {
        auto in = std::ifstream(path, std::ios::binary);
        return {
            std::istreambuf_iterator<char>(in),
            std::istreambuf_iterator<char>{}};
    }

    auto load_benchmark(TestMemory &test_memory, fs::path const &path)
    {
        MONAD_DEBUG_ASSERT(fs::is_directory(path));

        auto const contract_path = path / "contract";
        MONAD_DEBUG_ASSERT(fs::is_regular_file(contract_path));

        auto const calldata_path = path / "calldata";
        MONAD_DEBUG_ASSERT(fs::is_regular_file(calldata_path));

        return make_benchmark(
            test_memory,
            path.stem().string(),
            read_file(contract_path),
            read_file(calldata_path));
    }

    void precompile_contract(
        BlockchainTestVM *vm_ptr, evmc_revision rev, bytes32_t const &code_hash,
        uint8_t const *code, size_t const code_size)
    {
        (void)vm_ptr->get_code_analysis(code_hash, code, code_size);
        (void)vm_ptr->get_intercode_nativecode(rev, code_hash, code, code_size);
    }

    void precompile_contracts(
        BlockchainTestVM *vm_ptr, evmc_revision rev,
        JsonState const &json_state)
    {
        auto const test_state = json_state.make_test_state();
        for (auto const &addr : json_state.initial_accounts()) {
            auto const account = test_state->trie_db.read_account(addr);
            auto const code_hash = account.value().code_hash;
            auto const code = test_state->trie_db.read_code(code_hash);
            precompile_contract(
                vm_ptr, rev, code_hash, code->code(), code->size());
        }
    }

    // This benchmark runner assumes that no state is modified during execution,
    // as it re-uses the same state between all the runs. For anything other
    // that micro-benchmarks of e.g. specific opcodes, use the JSON format with
    // `run_benchmark_json`
    void run_benchmark(
        benchmark::State &bench_state,
        BlockchainTestVM::Implementation const impl, evmc_message const msg,
        std::vector<std::uint8_t> const &code)
    {
        auto vm = evmc::VM(new BlockchainTestVM(impl));

        auto const json_state = JsonState{};
        auto const test_state = json_state.make_test_state();
        vm::VM monad_vm;
        BlockState block_state{test_state->trie_db, monad_vm};
        monad::State state{
            block_state, Incarnation{json_state.header.number, 1}};

        TestBlockHashBuffer block_hash_buffer{};
        Transaction tx{};
        Address const tx_sender{};
        std::optional<uint256_t> base_fee_per_gas{};
        std::vector<std::optional<Address>> authorities{};
        BlockHeader const header{};
        EthereumMainnet const chain{};

        constexpr auto rev = EVMC_CANCUN;
        auto test_host = TestHost<EvmTraits<rev>>{
            block_hash_buffer,
            state,
            tx,
            tx_sender,
            base_fee_per_gas,
            authorities,
            header,
            chain};
        auto &host = test_host.get_evmc_host();

        auto *vm_ptr =
            reinterpret_cast<BlockchainTestVM *>(vm.get_raw_pointer());
        auto const *interface = &host.get_interface();
        evmc_host_context *ctx = host.to_context();

        auto code_hash = interface->get_code_hash(ctx, &msg.code_address);

        precompile_contract(vm_ptr, rev, code_hash, code.data(), code.size());

        for (auto _ : bench_state) {
            auto const result = evmc::Result{vm_ptr->execute(
                interface, ctx, rev, &msg, code.data(), code.size())};

            MONAD_ASSERT(result.status_code == EVMC_SUCCESS);
        }
    }

    void touch_init_state(JsonState const &json_state, monad::State &state)
    {
        for (auto const &addr : json_state.initial_accounts()) {
            state.touch(addr);
            state.get_code(addr);
        }
    };

    void run_benchmark_json(
        benchmark::State &bench_state,
        BlockchainTestVM::Implementation const impl,
        JsonState const &json_state, evmc_message const msg,
        bool assert_success)
    {
        auto vm = evmc::VM(new BlockchainTestVM(impl));
        auto *vm_ptr =
            reinterpret_cast<BlockchainTestVM *>(vm.get_raw_pointer());

        constexpr auto rev = EVMC_CANCUN;
        precompile_contracts(vm_ptr, rev, json_state);

        auto const test_state = json_state.make_test_state();
        auto const account = test_state->trie_db.read_account(msg.code_address);
        auto const code =
            test_state->trie_db.read_code(account.value().code_hash);

        TestBlockHashBuffer block_hash_buffer{};
        Transaction tx{};
        Address const tx_sender{};
        std::optional<uint256_t> base_fee_per_gas{};
        std::vector<std::optional<Address>> authorities{};
        BlockHeader const header{};
        EthereumMainnet const chain{};

        for (auto _ : bench_state) {
            bench_state.PauseTiming();

            vm::VM monad_vm;
            BlockState block_state{test_state->trie_db, monad_vm};
            monad::State state{
                block_state, Incarnation{json_state.header.number, 1}};

            touch_init_state(json_state, state);

            auto test_host = TestHost<EvmTraits<rev>>{
                block_hash_buffer,
                state,
                tx,
                tx_sender,
                base_fee_per_gas,
                authorities,
                header,
                chain};
            auto &host = test_host.get_evmc_host();

            auto const *interface = &host.get_interface();
            auto *ctx = host.to_context();
            bench_state.ResumeTiming();

            auto const result = evmc::Result{vm_ptr->execute(
                interface, ctx, rev, &msg, code->code(), code->size())};

            if (assert_success) {
                MONAD_ASSERT(result.status_code == EVMC_SUCCESS);
            }
            else {
                MONAD_ASSERT(result.status_code != EVMC_SUCCESS);
            }
        }
    }

    static BlockchainTestVM::Implementation const all_impls[] = {
        Interpreter,
        Compiler,
        Evmone,
    };

    void register_benchmark(
        std::string_view const name, evmc_message const msg,
        std::vector<std::uint8_t> const &code)
    {
        for (auto const impl : all_impls) {
            benchmark::RegisterBenchmark(
                std::format(
                    "execute/{}/{}", name, BlockchainTestVM::impl_name(impl)),
                run_benchmark,
                impl,
                msg,
                code);
        }
    }

    auto benchmarks(TestMemory &test_memory) noexcept
    {
        auto ret = std::vector<benchmark_case>{};

        for (auto const &p :
             fs::directory_iterator(execution_benchmarks_dir / "basic")) {
            ret.emplace_back(load_benchmark(test_memory, p));
        }

        return ret;
    }

    auto load_benchmark_json(std::filesystem::path const &json_test_file)
    {
        std::ifstream f{json_test_file};
        return load_benchmark_tests(f);
    }

    auto benchmarks_json()
    {
        return std::vector<std::vector<BenchmarkTest>>{
            load_benchmark_json(vm_performance_dir / "performanceTester.json"),
        };
    }

    void register_benchmark_json(
        std::vector<BenchmarkTest> const &tests, TestMemory &test_memory)
    {

        for (auto const &test : tests) {
            for (size_t block_no = 0; block_no < test.test_blocks.size();
                 ++block_no) {
                auto const &block = test.test_blocks[block_no];
                for (size_t i = 0; i < block.transactions.size(); ++i) {
                    auto const &tx = block.transactions[i];

                    auto const recipient = tx.to.value_or({});

                    auto const sender = recover_sender(tx).value();
                    auto msg = evmc_message{
                        .kind = tx.to.has_value() ? EVMC_CALL : EVMC_CREATE,
                        .flags = 0,
                        .depth = 0,
                        .gas = 150'000'000,
                        .recipient = recipient,
                        .sender = sender,
                        .input_data = tx.data.data(),
                        .input_size = tx.data.size(),
                        .value = intx::be::store<evmc::uint256be>(tx.value),
                        .create2_salt = {},
                        .code_address = recipient,
                        .memory_handle = test_memory.data,
                        .memory = test_memory.data,
                        .memory_capacity = TestMemory::capacity,
                    };

                    std::vector<std::string> const failure_tests = {
                        "delegatecall_slow_interpreter"};

                    bool const assert_success =
                        std::find(
                            failure_tests.begin(),
                            failure_tests.end(),
                            test.name) == failure_tests.end();

                    for (auto const impl : all_impls) {
                        benchmark::RegisterBenchmark(
                            std::format(
                                "execute/{}/{}/{}/{}",
                                test.name,
                                block_no,
                                i,
                                BlockchainTestVM::impl_name(impl)),
                            run_benchmark_json,
                            impl,
                            test.json_state,
                            msg,
                            assert_success);
                    }
                }
            }
        }
    }
}

int main(int argc, char **argv)
{
    TestMemory test_memory;
    auto const all_bms = benchmarks(test_memory);

    for (auto const &bm : all_bms) {
        register_benchmark(bm.name, *bm.msg, bm.code);
    }

    auto const all_bms_json = benchmarks_json();

    for (auto const &path : all_bms_json) {
        register_benchmark_json(path, test_memory);
    }

    benchmark::Initialize(&argc, argv);
    benchmark::RunSpecifiedBenchmarks();
    benchmark::Shutdown();
}
