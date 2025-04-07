#pragma once

#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/config.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <nlohmann/json_fwd.hpp>

#include <filesystem>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class TrieDb;
struct Block;
struct Receipt;

MONAD_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

struct EthereumMainnetRev : EthereumMainnet
{
    evmc_revision const rev;

    EthereumMainnetRev(evmc_revision const rev)
        : rev{rev}
    {
    }

    virtual evmc_revision get_revision(
        uint64_t /* block_number */, uint64_t /* timestamp */) const override
    {
        return rev;
    }
};

using db_t = monad::TrieDb;

class BlockchainSpecTest : public testing::Test
{
protected:
    static fiber::PriorityPool *pool_;

    std::filesystem::path const file_;
    std::optional<evmc_revision> const revision_;

    virtual Result<std::vector<Receipt>> execute_dispatch(
        evmc_revision, Block &, db_t &, BlockHashBuffer const &) = 0;

    void
    validate_post_state(nlohmann::json const &json, nlohmann::json const &db);

public:
    static void SetUpTestSuite();
    static void TearDownTestSuite();

    BlockchainSpecTest(
        std::filesystem::path const &file,
        std::optional<evmc_revision> const &revision) noexcept
        : file_{file}
        , revision_{revision}
    {
    }

    void TestBody() override;
};

MONAD_TEST_NAMESPACE_END
