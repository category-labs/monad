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

#include <category/vm/core/assert.h>

#include <test_resource_data.h>

#include <test_resource_data.h>
#include <test_vm.hpp>

#include "benchmarktest.hpp"

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include "host.hpp"
#include "state.hpp"
#include "test_state.hpp"

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

using namespace evmone::state;
using namespace monad::test_resource;

using enum BlockchainTestVM::Implementation;

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
        MONAD_VM_DEBUG_ASSERT(fs::is_directory(path));

        auto const contract_path = path / "contract";
        MONAD_VM_DEBUG_ASSERT(fs::is_regular_file(contract_path));

        auto const calldata_path = path / "calldata";
        MONAD_VM_DEBUG_ASSERT(fs::is_regular_file(calldata_path));

        return make_benchmark(
            test_memory,
            path.stem().string(),
            read_file(contract_path),
            read_file(calldata_path));
    }

    // This benchmark runner assumes that no state is modified during execution,
    // as it re-uses the same state between all the runs. For anything other
    // that micro-benchmarks of e.g. specific opcodes, use the JSON format with
    // `run_benchmark_json`
    void run_benchmark(
        benchmark::State &state, BlockchainTestVM::Implementation const impl,
        evmc_message const msg, std::vector<std::uint8_t> const &code)
    {
        auto vm = evmc::VM(new BlockchainTestVM(impl));
        auto const empty_test_state = evmone::test::TestState{};

        auto evm_state = State{empty_test_state};
        auto block = BlockInfo{};
        auto hashes = evmone::test::TestBlockHashes{};
        auto tx = Transaction{};

        auto rev = EVMC_CANCUN;
        auto host = Host(rev, vm, evm_state, block, hashes, tx);

        auto *vm_ptr =
            reinterpret_cast<BlockchainTestVM *>(vm.get_raw_pointer());
        auto const *interface = &host.get_interface();
        evmc_host_context *ctx = host.to_context();

        auto code_hash = interface->get_code_hash(ctx, &msg.code_address);

        vm_ptr->precompile_contract(
            rev, code_hash, code.data(), code.size(), impl);

        for (auto _ : state) {
            auto const result = evmc::Result{vm_ptr->execute(
                interface, ctx, rev, &msg, code.data(), code.size())};

            MONAD_VM_ASSERT(result.status_code == EVMC_SUCCESS);
        }
    }

    void touch_init_state(
        evmone::test::TestState const &init_state, evmone::state::State &state)
    {
        for (auto const &[addr, _] : init_state) {
            state.find(addr);
        }
    };

    void run_benchmark_json(
        benchmark::State &state, BlockchainTestVM::Implementation const impl,
        evmone::test::TestState const &initial_test_state,
        evmc_message const msg, bool assert_success)
    {

        auto vm = evmc::VM(new BlockchainTestVM(impl));
        auto *vm_ptr =
            reinterpret_cast<BlockchainTestVM *>(vm.get_raw_pointer());

        auto rev = EVMC_CANCUN;
        vm_ptr->precompile_contracts(rev, initial_test_state, impl);

        auto const code = initial_test_state.get_account_code(msg.code_address);

        for (auto _ : state) {
            state.PauseTiming();
            auto evm_state = State{initial_test_state};
            touch_init_state(initial_test_state, evm_state);
            auto const block = BlockInfo{};
            auto const hashes = evmone::test::TestBlockHashes{};
            auto const tx = Transaction{};

            auto host = Host(rev, vm, evm_state, block, hashes, tx);

            auto const *interface = &host.get_interface();
            auto *ctx = host.to_context();
            state.ResumeTiming();

            auto const result = evmc::Result{vm_ptr->execute(
                interface, ctx, rev, &msg, code.data(), code.size())};

            if (assert_success) {
                MONAD_VM_ASSERT(result.status_code == EVMC_SUCCESS);
            }
            else {
                MONAD_VM_ASSERT(result.status_code != EVMC_SUCCESS);
            }
        }
    }

    static BlockchainTestVM::Implementation const all_impls[] = {
        Interpreter,
        Compiler,
        Evmone,
#ifdef MONAD_COMPILER_LLVM
        LLVM,
#endif
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
        auto ret = std::vector<std::vector<BenchmarkTest>>{
            load_benchmark_json(vm_performance_dir / "performanceTester.json"),
        };
        return ret;
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

                    auto const recipient =
                        tx.to.has_value() ? *tx.to : evmc::address{};

                    auto msg = evmc_message{
                        .kind = tx.to.has_value() ? EVMC_CALL : EVMC_CREATE,
                        .flags = 0,
                        .depth = 0,
                        .gas = 150'000'000,
                        .recipient = recipient,
                        .sender = tx.sender,
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
                            test.pre_state,
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
