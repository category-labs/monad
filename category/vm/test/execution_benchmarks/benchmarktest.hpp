#pragma once

#include "state.hpp"
#include "statetest.hpp"
#include "test_state.hpp"

#include <evmc/evmc.hpp>
#include <span>
#include <vector>

using namespace evmone::state;

namespace monad::test
{
    struct UnsupportedTestFeature : std::runtime_error
    {
        using runtime_error::runtime_error;
    };

    struct TestBlock
    {
        std::vector<Transaction> transactions;
    };

    struct BenchmarkTest
    {

        std::string name;

        std::vector<TestBlock> test_blocks;
        evmone::test::TestState pre_state;
    };

    std::vector<BenchmarkTest> load_benchmark_tests(std::istream &input);
} // namespace monad::test
