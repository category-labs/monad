#include <ethereum_test.hpp>
#include <from_json.hpp>
#include <transaction_test.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/core.h>
#include <quill/detail/LogMacros.h>

#include <gtest/gtest.h>

#include <test_resource_data.h>

#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <string>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void register_tests(
    std::filesystem::path const &root,
    std::optional<evmc_revision> const &revision)
{
    namespace fs = std::filesystem;
    MONAD_ASSERT(fs::exists(root) && fs::is_directory(root));

    for (auto const &entry : fs::recursive_directory_iterator{root}) {
        auto const path = entry.path();
        if (path.extension() == ".json") {
            MONAD_ASSERT(entry.is_regular_file());

            auto test = fmt::format("{}", fs::relative(path, root).string());
            std::ranges::replace(test, '-', '_');

            testing::RegisterTest(
                "TransactionTests",
                test.c_str(),
                nullptr,
                nullptr,
                path.string().c_str(),
                0,
                [=] -> testing::Test * {
                    return new test::TransactionTest(path, revision);
                });
        }
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

template <evmc_revision rev>
void process_transaction(Transaction const &txn, nlohmann::json const &expected)
{
    if (auto const result = static_validate_transaction<rev>(
            txn, std::nullopt, 1, MAX_CODE_SIZE_EIP170);
        result.has_error()) {
        EXPECT_TRUE(expected.contains("exception"));
    }
    else {
        auto const sender = recover_sender(txn);
        if (!sender.has_value()) {
            EXPECT_TRUE(expected.contains("exception"));
        }
        else {
            EXPECT_FALSE(expected.contains("exception"));

            // check sender
            EXPECT_EQ(
                sender.value(), expected.at("sender").get<evmc::address>());

            // check gas
            EXPECT_EQ(
                intrinsic_gas<rev>(txn),
                integer_from_json<uint64_t>(expected.at("intrinsicGas")));
        }
    }
}

void process_transaction(
    evmc_revision const rev, Transaction const &txn,
    nlohmann::json const &expected)
{
    MONAD_ASSERT(rev != EVMC_CONSTANTINOPLE);
    SWITCH_EVMC_REVISION(process_transaction, txn, expected);
    MONAD_ASSERT(false);
}

void TransactionTest::TestBody()
{
    std::ifstream f{file_};

    bool executed = false;

    auto const json = nlohmann::json::parse(f);

    // There should be just 1 test per file
    auto const j_content = json.begin().value();
    auto const test_name = json.begin().key();
    MONAD_ASSERT(!j_content.empty());

    auto const txn_rlp = j_content.at("txbytes").get<byte_string>();
    byte_string_view txn_rlp_view{txn_rlp};
    auto const txn = rlp::decode_transaction(txn_rlp_view);
    if (txn.has_error() || !txn_rlp_view.empty()) {
        for (auto const &element : j_content.at("result").items()) {
            auto const &expected = element.value();
            EXPECT_TRUE(expected.contains("exception")) << test_name;
        }
        return;
    }

    for (auto const &element : j_content.at("result").items()) {
        auto const &fork_name = element.key();
        auto const &expected = element.value();

        if (!revision_map.contains(fork_name)) {
            LOG_ERROR(
                "Skipping {} due to missing support for fork {}",
                test_name,
                fork_name);
            continue;
        }

        auto const rev = revision_map.at(fork_name);
        if (revision_.has_value() && rev != revision_) {
            continue;
        }
        executed = true;

        process_transaction(rev, txn.value(), expected);
    }

    if (!executed) {
        MONAD_ASSERT(revision_.has_value());
        GTEST_SKIP() << "no test cases found for revision="
                     << revision_.value();
    }
}

void register_transaction_tests(std::optional<evmc_revision> const &revision)
{
    register_tests(
        test_resource::ethereum_tests_dir / "TransactionTests", revision);
    register_tests(
        test_resource::build_dir /
            "src/ExecutionSpecTestFixtures/transaction_tests",
        revision);
}

MONAD_TEST_NAMESPACE_END
