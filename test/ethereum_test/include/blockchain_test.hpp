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

#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json_fwd.hpp>

#include <filesystem>
#include <optional>
#include <variant>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
struct BlockExecOutput;
class BlockHashBuffer;
struct Receipt;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

class BlockchainTest : public testing::Test
{
    std::filesystem::path const file_;
    std::optional<std::variant<evmc_revision, monad_revision>> const revision_;
    bool enable_tracing_;

public:
    static void SetUpTestSuite();
    static void TearDownTestSuite();

    BlockchainTest(
        std::filesystem::path const &file,
        std::optional<std::variant<evmc_revision, monad_revision>> const
            &revision,
        bool enable_tracing) noexcept
        : file_{file}
        , revision_{revision}
        , enable_tracing_{enable_tracing}
    {
    }

    void TestBody() override;
};

void register_blockchain_tests_path(
    std::filesystem::path const &,
    std::optional<std::variant<evmc_revision, monad_revision>> const &, bool);

void register_blockchain_tests(
    std::optional<std::variant<evmc_revision, monad_revision>> const &, bool);

MONAD_TEST_NAMESPACE_END
