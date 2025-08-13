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

#include "test_vm.hpp"

#include <test_resource_data.h>

#include <blockchaintest.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <filesystem>

using namespace evmone::test;

int main(int argc, char **argv)
{
    auto const root =
        monad::test_resource::ethereum_tests_dir / "BlockchainTests";

    init_llvm();

    auto vm =
        evmc::VM{new BlockchainTestVM(BlockchainTestVM::Implementation::LLVM)};
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
