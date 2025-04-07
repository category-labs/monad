#include <monad/config.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/execution/trace/event_trace.hpp>

#include <ethereum_test.hpp>
#include <transaction_test.hpp>

#include <evmc/evmc.h>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <string>
#include <unordered_map>

MONAD_NAMESPACE_BEGIN

quill::Logger *event_tracer = nullptr;

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;
    testing::InitGoogleTest(&argc, argv); // Process GoogleTest flags.

    auto log_level = quill::LogLevel::None;
    std::optional<evmc_revision> revision = std::nullopt;
    std::optional<size_t> txn_index = std::nullopt;

    CLI::App app{"monad ethereum tests runner"};
    app.add_option("--log_level", log_level, "Logging level")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    app.add_option("--fork", revision, "Fork to run unit tests for")
        ->transform(
            CLI::CheckedTransformer(test::revision_map, CLI::ignore_case));
    app.add_option("--txn", txn_index, "Index of transaction to run");
    CLI11_PARSE(app, argc, argv);

    quill::start(true);
    quill::get_root_logger()->set_log_level(log_level);
#ifdef ENABLE_EVENT_TRACING
    event_tracer = quill::create_logger("event_trace", quill::null_handler());
#endif

    test::register_ethereum_blockchain_tests(revision);
    test::register_transaction_tests(revision);

    int return_code = RUN_ALL_TESTS();

    if (::testing::UnitTest::GetInstance()->test_to_run_count() == 0) {
        LOG_ERROR("No tests were run.");
        return_code = -1;
    }

    quill::flush();

    return return_code;
}
