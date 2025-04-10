#pragma once

#include <spec_test_utils.hpp>

#include <monad/core/result.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json_fwd.hpp>

#include <filesystem>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
struct Receipt;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

class EthereumSpecTest : public testing::Test
{
    static fiber::PriorityPool *pool_;

    std::filesystem::path const file_;
    std::optional<evmc_revision> const revision_;

    template <evmc_revision rev>
    static Result<std::vector<Receipt>>
    execute(Block &, test::db_t &, BlockHashBuffer const &);

    static Result<std::vector<Receipt>> execute_dispatch(
        evmc_revision, Block &, test::db_t &, BlockHashBuffer const &);

public:
    static void SetUpTestSuite();
    static void TearDownTestSuite();

    EthereumSpecTest(
        std::filesystem::path const &file,
        std::optional<evmc_revision> const &revision) noexcept
        : file_{file}
        , revision_{revision}
    {
    }

    void TestBody() override;
};

void register_ethereum_blockchain_tests(std::optional<evmc_revision> const &);

MONAD_TEST_NAMESPACE_END
