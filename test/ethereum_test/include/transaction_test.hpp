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

#include <category/vm/evm/monad/revision.h>
#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>

#include <filesystem>
#include <optional>
#include <variant>

MONAD_TEST_NAMESPACE_BEGIN

class TransactionTest : public testing::Test
{
private:
    std::filesystem::path const file_;
    std::optional<std::variant<evmc_revision, monad_revision>> const revision_;

public:
    TransactionTest(
        std::filesystem::path const &file,
        std::optional<std::variant<evmc_revision, monad_revision>> const
            &revision) noexcept
        : file_{file}
        , revision_{revision}
    {
    }

    void TestBody() override;
};

void register_transaction_tests_path(
    std::filesystem::path const &,
    std::optional<std::variant<evmc_revision, monad_revision>> const &);

void register_transaction_tests(
    std::optional<std::variant<evmc_revision, monad_revision>> const &);

MONAD_TEST_NAMESPACE_END
