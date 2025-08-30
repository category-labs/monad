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

#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/evm/chain.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/utils/load_program.hpp>

#include <test_resource_data.h>

#include <benchmark/benchmark.h>

#include <evmc/evmc.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <format>
#include <fstream>
#include <ios>
#include <iterator>
#include <random>
#include <vector>

namespace fs = std::filesystem;

namespace
{
    class RandomFixture : public benchmark::Fixture
    {
    public:
        void SetUp(benchmark::State &)
        {
            engine_ = std::default_random_engine{0};
        }

        void TearDown(benchmark::State &) {}

        std::uint8_t random_byte()
        {
            return dist_(engine_);
        }

    private:
        std::default_random_engine engine_{0};
        std::uniform_int_distribution<std::uint8_t> dist_;
    };

    // clang-format off: formatter breaks on this macro structure
    BENCHMARK_DEFINE_F(RandomFixture, complexity_random_bytes)(benchmark::State &state)
    // clang-format on
    {
        auto size = state.range(0);

        auto program = std::vector<std::uint8_t>{};
        program.reserve(static_cast<std::size_t>(size));
        std::generate_n(std::back_inserter(program), size, [this] {
            return random_byte();
        });

        MONAD_VM_ASSERT(
            program.size() <= *monad::vm::interpreter::code_size_t::max());
        auto rt = asmjit::JitRuntime{};

        for (auto _ : state) {
            auto fn = monad::vm::compiler::native::compile<
                monad::EvmChain<EVMC_LATEST_STABLE_REVISION>>(
                rt,
                program.data(),
                monad::vm::interpreter::code_size_t::unsafe_from(
                    static_cast<uint32_t>(program.size())));

            if (!fn) {
                return state.SkipWithError("Failed to compile contract");
            }
        }

        state.counters["codesize"] = static_cast<double>(program.size());
        state.SetComplexityN(size);
    }

    BENCHMARK_REGISTER_F(RandomFixture, complexity_random_bytes)
        ->Name("complexity_random_bytes")
        ->RangeMultiplier(2)
        ->Range(1, 24 * 1024)
        ->Complexity();

    void run_benchmark(benchmark::State &state, fs::path const &evm_code)
    {
        std::ifstream file(evm_code, std::ios::ate);
        auto const size = file.tellg();
        if (size == 0) {
            return state.SkipWithError("Failed to open file");
        }
        file.seekg(0, std::ios::beg);

        std::vector<char> buffer(static_cast<size_t>(size));
        file.read(buffer.data(), size);

        auto program = monad::vm::utils::parse_hex_program(buffer);
        MONAD_VM_ASSERT(
            program.size() <= *monad::vm::interpreter::code_size_t::max());

        auto rt = asmjit::JitRuntime{};

        for (auto _ : state) {
            auto ncode = monad::vm::compiler::native::compile<
                monad::EvmChain<EVMC_LATEST_STABLE_REVISION>>(
                rt,
                program.data(),
                monad::vm::interpreter::code_size_t::unsafe_from(
                    static_cast<uint32_t>(program.size())));

            if (!ncode->entrypoint()) {
                return state.SkipWithError("Failed to compile contract");
            }
        }

        state.counters["codesize"] = static_cast<double>(program.size());
    }

    auto benchmark_tests()
    {
        return std::array{
            monad::test_resource::compile_benchmarks_dir / "usdt",
            monad::test_resource::compile_benchmarks_dir / "stop",
            monad::test_resource::compile_benchmarks_dir / "uniswap",
            monad::test_resource::compile_benchmarks_dir / "uniswap_v3",
        };
    }

    void register_benchmarks()
    {
        for (auto const &test : benchmark_tests()) {
            auto stem = test.stem();

            benchmark::RegisterBenchmark(
                std::format("compile/{}", stem.string()), run_benchmark, test);
        }
    }
}

int main(int argc, char **argv)
{
    register_benchmarks();

    benchmark::Initialize(&argc, argv);
    benchmark::RunSpecifiedBenchmarks();
}
