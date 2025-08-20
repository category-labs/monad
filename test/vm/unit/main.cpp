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

#include "test_params.hpp"

#include <monad/test/environment.hpp>

#include <CLI/CLI.hpp>
#include <filesystem>
#include <gtest/gtest.h>

int main(int argc, char *argv[])
{
    // Process GoogleTest flags.
    testing::InitGoogleTest(&argc, argv);
    testing::AddGlobalTestEnvironment(new monad::test::Environment);

    // Then our own flags.
    CLI::App app{"Monad VM unit tests", "vm-unit-tests"};
    app.add_flag(
        "--dump-asm",
        monad::vm::compiler::test::params.dump_asm_on_failure,
        "Save assembly on failure");
    CLI11_PARSE(app, argc, argv);

    // Create test log directory
    std::filesystem::path test_log_dir = "/tmp/monad_vm_test_logs";
    bool const needs_test_logs =
        monad::vm::compiler::test::params.dump_asm_on_failure;
    if (needs_test_logs && !std::filesystem::exists(test_log_dir)) {
        std::filesystem::create_directory(test_log_dir);
    }

    return RUN_ALL_TESTS();
}
