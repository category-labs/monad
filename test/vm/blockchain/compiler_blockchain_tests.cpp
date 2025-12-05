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

#include "gtest_filter.hpp"
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
    testing::FLAGS_gtest_filter += base_gtest_filter;

    return blockchain_test_main({root}, false, vm);
}
