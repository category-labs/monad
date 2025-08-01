#include <monad/vm/compiler/ir/x86.hpp>
#include <monad/vm/utils/load_program.hpp>

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

        auto rt = asmjit::JitRuntime{};

        for (auto _ : state) {
            auto fn = monad::vm::compiler::native::compile(
                rt, program, EVMC_LATEST_STABLE_REVISION);

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

        auto rt = asmjit::JitRuntime{};

        for (auto _ : state) {
            auto ncode = monad::vm::compiler::native::compile(
                rt, program, EVMC_LATEST_STABLE_REVISION);

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
