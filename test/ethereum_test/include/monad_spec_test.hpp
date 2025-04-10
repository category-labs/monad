#pragma once

#include <spec_test_utils.hpp>

#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <filesystem>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct Receipt;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

class MonadSpecTest : public testing::Test
{
    static fiber::PriorityPool *pool_;

    std::filesystem::path const file_;
    std::optional<evmc_revision> const revision_;

    template <evmc_revision rev>
    Result<std::vector<Receipt>>
    execute(Block &, db_t &, BlockHashBuffer const &);

    Result<std::vector<Receipt>>
    execute_dispatch(evmc_revision, Block &, db_t &, BlockHashBuffer const &);

public:
    static void SetUpTestSuite();
    static void TearDownTestSuite();

    MonadSpecTest(
        std::filesystem::path const &file,
        std::optional<evmc_revision> const &revision) noexcept
        : file_{file}
        , revision_{revision}
    {
    }

    void TestBody() override;
};

void register_monad_blockchain_tests(std::optional<evmc_revision> const &);

MONAD_TEST_NAMESPACE_END
