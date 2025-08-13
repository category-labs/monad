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

#pragma once

#include <category/vm/vm.hpp>

#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <span>

namespace fs = std::filesystem;

namespace monad::vm::compiler::test
{
    class EvmTest : public testing::Test
    {
    protected:
        enum Implementation
        {
            Compiler,
            Interpreter,
            Evmone,
        };

        EvmTest() noexcept = default;

        monad::vm::VM vm_{};

        evmc_revision rev_ = EVMC_CANCUN;

        evmc_message msg_{};

        evmc::MockedHost host_;

        evmc::Result result_;

        std::span<uint8_t const> output_data_{};

        void pre_execute(
            std::int64_t gas_limit,
            std::span<std::uint8_t const> calldata) noexcept;

        void execute(
            std::int64_t gas_limit, std::span<std::uint8_t const> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept;

        void execute(
            std::int64_t gas_limit, std::initializer_list<std::uint8_t> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept;

        void execute(
            std::span<std::uint8_t const> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept;

        void execute(
            std::initializer_list<std::uint8_t> code,
            std::span<std::uint8_t const> calldata = {},
            Implementation impl = Compiler) noexcept;

        void execute_and_compare(
            std::int64_t gas_limit, std::span<std::uint8_t const> code,
            std::span<std::uint8_t const> calldata = {}) noexcept;

        void execute_and_compare(
            std::int64_t gas_limit, std::initializer_list<std::uint8_t> code,
            std::span<std::uint8_t const> calldata = {}) noexcept;

        bool has_empty_state() const noexcept;
    };

    class EvmFile
        : public EvmTest
        , public testing::WithParamInterface<fs::directory_entry>
    {
    };
}
