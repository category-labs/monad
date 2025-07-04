#include "test_vm.hpp"

#include <test_resource_data.h>

#include <blockchaintest.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <filesystem>

using namespace monad;
using namespace monad::vm::compiler;

using namespace evmc::literals;
using namespace evmone::test;

namespace fs = std::filesystem;

int main(int argc, char **argv)
{
    auto const root = test_resource::ethereum_tests_dir / "BlockchainTests";

    auto vm = evmc::VM{
        new BlockchainTestVM(BlockchainTestVM::Implementation::Compiler)};
    blockchain_test_setup(&argc, argv);

    // Skip slow and broken tests:
    testing::FLAGS_gtest_filter +=
        ":-"
        // Slow
        "GeneralStateTests/VMTests/vmPerformance.loopExp:"
        "GeneralStateTests/VMTests/vmPerformance.loopMul:"
        "GeneralStateTests/stTimeConsuming.CALLBlake2f_MaxRounds:"
        "GeneralStateTests/stTimeConsuming.static_Call50000_sha256:"
        // Broken until https://github.com/ethereum/evmone/pull/1241 is included
        // in a release
        "InvalidBlocks/bcEIP1559.badBlocks:"
        "InvalidBlocks/bcEIP1559.badUncles:"
        "InvalidBlocks/bcEIP1559.gasLimit20m:"
        "InvalidBlocks/bcEIP1559.gasLimit40m:"
        "InvalidBlocks/bcMultiChainTest.UncleFromSideChain:"
        "InvalidBlocks/bcUncleTest.UncleIsBrother:"
        // Currently skipped on ethereum/evmone master
        "ValidBlocks/bcValidBlockTest.SimpleTx3LowS";

    return blockchain_test_main({root}, false, vm);
}
