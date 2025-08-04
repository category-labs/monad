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
