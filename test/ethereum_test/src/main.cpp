#include <ethereum_test.hpp>

#include <CLI/CLI.hpp>

#include <test_resource_data.h>

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

    auto *ethereum_test_logger =
        monad::log::logger_t::create_logger("ethereum_test_logger");
    auto *trie_db_logger =
        monad::log::logger_t::create_logger("trie_db_logger");
    auto *change_set_logger =
        monad::log::logger_t::create_logger("change_set_logger");
    auto *evmone_baseline_interpreter_logger =
        monad::log::logger_t::create_logger(
            "evmone_baseline_interpreter_logger");
    auto *state_logger = monad::log::logger_t::create_logger("state_logger");

    monad::log::level_t ethereum_test_log_level = quill::LogLevel::None;
    monad::log::level_t trie_db_log_level = quill::LogLevel::None;
    monad::log::level_t change_set_log_level = quill::LogLevel::None;
    monad::log::level_t evmone_baseline_interpreter_log_level =
        quill::LogLevel::None;
    monad::log::level_t state_log_level = quill::LogLevel::None;
    std::optional<size_t> fork_index = std::nullopt;
    std::optional<size_t> txn_index = std::nullopt;

    testing::InitGoogleTest(&argc, argv); // Process GoogleTest flags.

    // The default test filter. To enable all tests use `--gtest_filter=*`.
    testing::FLAGS_gtest_filter +=
        ":-stCreateTest.CreateOOGafterMaxCodesize:" // slow test
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

    auto *log_levels = app.add_subcommand("log_levels", "level of logging");
    log_levels
        ->add_option(
            "--ethereum_test", ethereum_test_log_level, "Log level for block")
        ->transform(CLI::CheckedTransformer(log_levels_map, CLI::ignore_case));
    log_levels
        ->add_option(
            "--change_set", change_set_log_level, "Log level for change_set")
        ->transform(CLI::CheckedTransformer(log_levels_map, CLI::ignore_case));
    log_levels
        ->add_option(
            "--evmone",
            evmone_baseline_interpreter_log_level,
            "Log level for evmone interpreter")
        ->transform(CLI::CheckedTransformer(log_levels_map, CLI::ignore_case));
    log_levels
        ->add_option("--trie_db", trie_db_log_level, "Log level for trie_db")

        ->transform(CLI::CheckedTransformer(log_levels_map, CLI::ignore_case));
    log_levels->add_option("--state", state_log_level, "Log level for state")
        ->transform(CLI::CheckedTransformer(log_levels_map, CLI::ignore_case));

    app.add_option("--fork", fork_index, "Fork to run unit tests for")
        ->transform(CLI::CheckedTransformer(
            monad::test::fork_index_map, CLI::ignore_case));

    app.add_option("--txn", txn_index, "Index of transaction to run");

    CLI11_PARSE(app, argc, argv);

    monad::log::logger_t::set_log_level(
        "ethereum_test_logger", ethereum_test_log_level);
    monad::log::logger_t::set_log_level(
        "change_set_logger", change_set_log_level);
    monad::log::logger_t::set_log_level(
        "evmone_baseline_interpreter_logger",
        evmone_baseline_interpreter_log_level);
    monad::log::logger_t::set_log_level("trie_db_logger", trie_db_log_level);
    monad::log::logger_t::set_log_level("state_logger", state_log_level);
    monad::log::logger_t::start();

    // only worrying about GeneralStateTests folder for now
    monad::test::EthereumTests::register_test_files(
        monad::test_resource::ethereum_tests_dir / "GeneralStateTests",
        fork_index,
        txn_index);

    int return_code = RUN_ALL_TESTS();

    quill::flush();
    quill::remove_logger(ethereum_test_logger);
    quill::remove_logger(trie_db_logger);
    quill::remove_logger(change_set_logger);
    quill::remove_logger(evmone_baseline_interpreter_logger);
    quill::remove_logger(state_logger);

    return return_code;
}
