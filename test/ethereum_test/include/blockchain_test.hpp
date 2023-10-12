#pragma once

#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>

#include <filesystem>
#include <optional>

MONAD_TEST_NAMESPACE_BEGIN

class BlockchainTest : public testing::Test
{
private:
    std::filesystem::path const file_;
    std::optional<evmc_revision> const revision_;

public:
    BlockchainTest(
        std::filesystem::path const &file,
        std::optional<evmc_revision> const &revision) noexcept
        : file_{file}
        , revision_{revision}
    {
    }

    void TestBody() override;
};

void register_blockchain_tests(std::optional<evmc_revision> const &);

MONAD_TEST_NAMESPACE_END
