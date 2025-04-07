#pragma once

#include <blockchain_spec_test.hpp>

#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <string>
#include <unordered_map>

MONAD_NAMESPACE_BEGIN

class State;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

class MonadSpecTest : public BlockchainSpecTest
{
    template <evmc_revision rev>
    Result<std::vector<Receipt>>
    execute(Block &, db_t &, BlockHashBuffer const &);

    Result<std::vector<Receipt>> execute_dispatch(
        evmc_revision, Block &, db_t &, BlockHashBuffer const &) override;

public:
    MonadSpecTest(
        std::filesystem::path const &file,
        std::optional<evmc_revision> const &revision) noexcept
        : BlockchainSpecTest(file, revision)
    {
    }
};

void register_monad_blockchain_tests(std::optional<evmc_revision> const &);

MONAD_TEST_NAMESPACE_END
