#include <general_state_test.hpp>
#include <test_resource_data.h>

#include <CLI/CLI.hpp>
#include <evmc/evmc.hpp>
#include <gtest/gtest.h>
#include <quill/Quill.h>

#include <unordered_map>

namespace
{
    std::unordered_map<std::string, quill::LogLevel> const log_levels_map = {
        {"tracel3", quill::LogLevel::TraceL3},
        {"trace_l3", quill::LogLevel::TraceL3},
        {"tracel2", quill::LogLevel::TraceL2},
        {"trace_l2", quill::LogLevel::TraceL2},
        {"tracel1", quill::LogLevel::TraceL1},
        {"trace_l1", quill::LogLevel::TraceL1},
        {"debug", quill::LogLevel::Debug},
        {"info", quill::LogLevel::Info},
        {"warning", quill::LogLevel::Warning},
        {"error", quill::LogLevel::Error},
        {"critical", quill::LogLevel::Critical},
        {"backtrace", quill::LogLevel::Backtrace},
        {"none", quill::LogLevel::None},
        {"dynamic", quill::LogLevel::Dynamic}};
}

int main(int argc, char *argv[])
{
    auto log_level = quill::LogLevel::None;
    std::optional<evmc_revision> revision = std::nullopt;
    std::optional<size_t> txn_index = std::nullopt;

    testing::InitGoogleTest(&argc, argv); // Process GoogleTest flags.

    // The default test filter. To enable all tests use `--gtest_filter=*`.
    testing::FLAGS_gtest_filter +=
        ":-:stCreateTest.CreateOOGafterMaxCodesize:" // slow test
        "stQuadraticComplexityTest.Call50000_sha256:" // slow test
        "stTimeConsuming.static_Call50000_sha256:" // slow test
        "stTimeConsuming.CALLBlake2f_MaxRounds:" // slow test
        "VMTests/vmPerformance.*:" // slow test

        // this test causes the test harness to crash when
        // parsing because it tries to parse
        // "0x031eea408f8e1799cb883da2927b1336521d73c2c14accfebb70d5c5af006c"
        // which causes stoull to throw an std::out_of_range exception
        "stTransactionTest.HighGasPrice:"
        "stTransactionTest.ValueOverflow";

    CLI::App app{"monad ethereum tests runner"};

    app.add_option("--log_level", log_level, "Logging level")
        ->transform(CLI::CheckedTransformer(log_levels_map, CLI::ignore_case));

    app.add_option("--fork", revision, "Fork to run unit tests for")
        ->transform(CLI::CheckedTransformer(
            monad::test::revision_map, CLI::ignore_case));

    app.add_option("--txn", txn_index, "Index of transaction to run");

    CLI11_PARSE(app, argc, argv);

    quill::start(true);

    quill::get_root_logger()->set_log_level(log_level);

    // only worrying about GeneralStateTests folder for now
    monad::test::register_general_state_tests(revision, txn_index);

    int return_code = RUN_ALL_TESTS();

    if (::testing::UnitTest::GetInstance()->test_to_run_count() == 0) {
        LOG_ERROR("No tests were run.");
        return_code = -1;
    }

    quill::flush();

    return return_code;
}
