#pragma once

#include <ethereum_test.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <nlohmann/json.hpp>

#include <filesystem>
#include <optional>
#include <string>

MONAD_TEST_NAMESPACE_BEGIN

class GeneralStateTest : public testing::Test
{
private:
    std::filesystem::path const json_test_file_;
    std::optional<evmc_revision> const revision_;
    std::optional<size_t> const txn_index_;

public:
    GeneralStateTest(
        std::filesystem::path const &json_test_file,
        std::optional<evmc_revision> const &revision,
        std::optional<size_t> const &txn_index) noexcept
        : json_test_file_{json_test_file}
        , revision_{revision}
        , txn_index_(txn_index)
    {
    }

    void TestBody() override;
};

void register_general_state_tests(
    std::optional<evmc_revision> const &,
    std::optional<size_t> const &txn_index);

MONAD_TEST_NAMESPACE_END
