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
#include <category/core/int.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/vm/code.hpp>
#include <category/vm/compiler.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/jumpdest_scan.hpp>
#include <category/vm/vm.hpp>

#include <test_resource_data.h>

#include <test/vm/utils/benchmark_vm.hpp>
#include <test/vm/utils/test_block_hash_buffer.hpp>
#include <test/vm/utils/test_host.hpp>
#include <test/vm/utils/test_memory.hpp>

#include "benchmarktest.hpp"

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

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
#include <random>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace fs = std::filesystem;

namespace json = nlohmann;

using namespace monad::test_resource;

using namespace monad;
using namespace monad::test;

using monad::vm::test::impl_name;
using monad::vm::test::prime_varcode_cache;
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
    std::vector<uint8_t> code;
};

namespace
{
    auto vm_performance_dir = monad::test_resource::ethereum_tests_dir /
                              "BlockchainTests" / "GeneralStateTests" /
                              "VMTests" / "vmPerformance";

    auto make_benchmark(
        TestMemory &test_memory, std::string const &name,
        std::span<uint8_t const> code, std::span<uint8_t const> input)
    {
        std::vector<uint8_t> code_buffer(code.begin(), code.end());

        auto *input_buffer = new uint8_t[input.size()];
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

    std::vector<uint8_t> read_file(fs::path const &path)
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

    constexpr auto rev = MONAD_LATEST_STABLE_REVISION;

    // Lift the native code size bound so every benchmark contract compiles.
    vm::CompilerConfig const compiler_config{
        .max_code_size_offset = vm::interpreter::code_size_t::max()};

    void prime_contracts(vm::VM &monad_vm, JsonState const &json_state)
    {
        auto const test_state = json_state.make_test_state();
        for (auto const &addr : json_state.initial_accounts()) {
            auto const account = test_state->trie_db.read_account(addr);
            auto const code_hash = account.value().code_hash;
            (void)prime_varcode_cache<MonadTraits<rev>>(
                monad_vm, code_hash, test_state->trie_db.read_code(code_hash));
        }
    }

    // This benchmark runner assumes that no state is modified during execution,
    // as it re-uses the same state between all the runs. For anything other
    // that micro-benchmarks of e.g. specific opcodes, use the JSON format with
    // `run_benchmark_json`
    void run_benchmark(
        benchmark::State &bench_state, vm::VM::Mode const mode,
        evmc_message const msg, std::vector<uint8_t> const &code)
    {
        vm::VM monad_vm{mode};
        monad_vm.set_compiler_config(compiler_config);

        auto const json_state = JsonState{};
        auto const test_state = json_state.make_test_state();
        BlockState block_state{test_state->trie_db, monad_vm};
        monad::State state{
            block_state, Incarnation{json_state.header.number + 1, 1}};

        state.create_contract(msg.code_address);
        state.set_code(msg.code_address, {code.data(), code.size()});

        TestBlockHashBuffer block_hash_buffer{};
        Transaction tx{};
        Address const tx_sender{};
        std::optional<uint256_t> base_fee_per_gas{};
        std::vector<std::optional<Address>> authorities{};
        BlockHeader const header{.number = json_state.header.number + 1};
        EthereumMainnet const chain{};

        auto test_host = TestHost<MonadTraits<rev>>{
            block_hash_buffer,
            state,
            tx,
            tx_sender,
            base_fee_per_gas,
            authorities,
            header,
            chain};

        auto const code_hash = state.get_code_hash(msg.code_address);
        auto const vcode = prime_varcode_cache<MonadTraits<rev>>(
            monad_vm, code_hash, state.get_code(msg.code_address)->intercode());

        for (auto _ : bench_state) {
            auto const result = monad_vm.execute<MonadTraits<rev>>(
                test_host.get_evmc_host(), &msg, code_hash, vcode);

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
        benchmark::State &bench_state, vm::VM::Mode const mode,
        JsonState const &json_state, evmc_message const msg,
        bool assert_success)
    {
        vm::VM monad_vm{mode};
        monad_vm.set_compiler_config(compiler_config);
        prime_contracts(monad_vm, json_state);

        auto const test_state = json_state.make_test_state();
        auto const account = test_state->trie_db.read_account(msg.code_address);
        auto const code_hash = account.value().code_hash;
        auto const code = test_state->trie_db.read_code(code_hash);

        TestBlockHashBuffer block_hash_buffer{};
        Transaction tx{};
        Address const tx_sender{};
        std::optional<uint256_t> base_fee_per_gas{};
        std::vector<std::optional<Address>> authorities{};
        BlockHeader const header{.number = json_state.header.number + 1};
        EthereumMainnet const chain{};

        for (auto _ : bench_state) {
            bench_state.PauseTiming();

            BlockState block_state{test_state->trie_db, monad_vm};
            monad::State state{
                block_state, Incarnation{json_state.header.number + 1, 1}};

            touch_init_state(json_state, state);

            auto test_host = TestHost<MonadTraits<rev>>{
                block_hash_buffer,
                state,
                tx,
                tx_sender,
                base_fee_per_gas,
                authorities,
                header,
                chain};

            auto const vcode = state.get_code(msg.code_address);
            bench_state.ResumeTiming();

            // Creation runs the code through the interpreter, as calls
            // through the compiled path.
            auto const result =
                msg.kind == EVMC_CREATE
                    ? monad_vm.execute_bytecode<MonadTraits<rev>>(
                          test_host.get_evmc_host(), &msg, code->code_span())
                    : monad_vm.execute<MonadTraits<rev>>(
                          test_host.get_evmc_host(), &msg, code_hash, vcode);

            if (assert_success) {
                MONAD_ASSERT(result.status_code == EVMC_SUCCESS);
            }
            else {
                MONAD_ASSERT(result.status_code != EVMC_SUCCESS);
            }
        }
    }

    // JUMPDEST-scan microbenchmark: the SIMD kernel against the scalar fallback
    // on identical buffers. Both kernels are compiled on AVX2 builds (the
    // scalar one is also the production path without AVX2), so this times them
    // directly rather than through a CREATE.
    std::vector<uint8_t>
    make_scan_code(std::string_view const pattern, size_t const n)
    {
        // 32 trailing zero bytes: the AVX2 kernel reads code in 32-byte steps.
        std::vector<uint8_t> v(n + 32, 0);
        std::mt19937_64 rng(0xC0FFEE);
        if (pattern == "random") {
            for (size_t i = 0; i < n; ++i) {
                v[i] = static_cast<uint8_t>(rng() & 0xff);
            }
        }
        else if (pattern == "branchy") {
            // Independent JUMPDEST/PUSH1 coin flips, so the scalar scan's
            // is-PUSH branch is unpredictable.
            for (size_t i = 0; i < n; ++i) {
                v[i] = static_cast<uint8_t>((rng() & 1) ? 0x60 : 0x5b);
            }
        }
        else if (pattern == "jumpdest_add") {
            // Independent JUMPDEST/ADD coin flips: the scalar scan visits every
            // byte, and its is-JUMPDEST branch is unpredictable.
            for (size_t i = 0; i < n; ++i) {
                v[i] = static_cast<uint8_t>((rng() & 1) ? 0x5b : 0x01);
            }
        }
        else if (pattern == "push_dense") {
            // PUSH32, which the scalar scan skips 32 at a time.
            std::fill_n(v.begin(), n, static_cast<uint8_t>(0x7f));
        }
        else {
            MONAD_ASSERT(false);
        }
        return v;
    }

    using scan_fn = void (*)(uint8_t const *, size_t, uint64_t *);

    void run_jumpdest_scan_benchmark(
        benchmark::State &bench_state, scan_fn const scan,
        std::vector<uint8_t> const &code, size_t const n)
    {
        std::vector<uint64_t> bits(
            vm::interpreter::detail::jumpdest_word_count(n), 0);
        for (auto _ : bench_state) {
            scan(code.data(), n, bits.data());
            benchmark::DoNotOptimize(bits.data());
            benchmark::ClobberMemory();
        }
        bench_state.SetBytesProcessed(
            static_cast<int64_t>(bench_state.iterations()) *
            static_cast<int64_t>(n));
    }

    void register_jumpdest_scan_benchmarks()
    {
        size_t const n = 256 * 1024;
        for (auto const *const pattern :
             {"random", "branchy", "jumpdest_add", "push_dense"}) {
            benchmark::RegisterBenchmark(
                std::format("jumpdest_scan/scalar/{}", pattern),
                run_jumpdest_scan_benchmark,
                &vm::interpreter::detail::find_jumpdests_scalar,
                make_scan_code(pattern, n),
                n);
#if defined(__AVX2__)
            benchmark::RegisterBenchmark(
                std::format("jumpdest_scan/avx2/{}", pattern),
                run_jumpdest_scan_benchmark,
                &vm::interpreter::detail::find_jumpdests_avx2,
                make_scan_code(pattern, n),
                n);
#endif
        }
    }

    static vm::VM::Mode const all_impls[] = {
        vm::VM::InterpreterOnly,
        vm::VM::CompilerOnly,
    };

    void register_benchmark(
        std::string_view const name, evmc_message const msg,
        std::vector<uint8_t> const &code)
    {
        for (auto const impl : all_impls) {
            benchmark::RegisterBenchmark(
                std::format("execute/{}/{}", name, impl_name(impl)),
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
                        .value = store_be_as<evmc::uint256be>(tx.value),
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
                                impl_name(impl)),
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

    register_jumpdest_scan_benchmarks();

    benchmark::Initialize(&argc, argv);
    benchmark::RunSpecifiedBenchmarks();
    benchmark::Shutdown();
}
