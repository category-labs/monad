// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/log_level_map.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/vm/evm/monad/revision.h>

#include <blockchain_test.hpp>
#include <event.hpp>
#include <monad/test/config.hpp>
#include <revision_map.hpp>
#include <transaction_test.hpp>

#include <evmc/evmc.h>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <gtest/gtest.h>

#include <chrono>
#include <cstddef>
#include <optional>
#include <string>
#include <thread>
#include <unordered_map>
#include <variant>

MONAD_NAMESPACE_BEGIN

quill::Logger *event_tracer = nullptr;

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;
    testing::InitGoogleTest(&argc, argv); // Process GoogleTest flags.

    auto log_level = quill::LogLevel::None;
    std::optional<std::string> fork_name;
    std::optional<std::variant<evmc_revision, monad_revision>> revision =
        std::nullopt;
    std::optional<size_t> txn_index = std::nullopt;
    std::string record_exec_events_path;
    std::optional<std::filesystem::path> blockchain_tests_path;
    std::optional<std::filesystem::path> transaction_tests_path;
    bool trace_calls = false;
    unsigned sleep_seconds = 0;

    CLI::App app{"monad ethereum tests runner"};
    app.add_option("--log_level", log_level, "Logging level")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    app.add_option("--fork", fork_name, "Fork to run unit tests for")
        ->transform(CLI::IsMember(
            std::views::keys(test::revision_map) | std::ranges::to<std::set>(),
            CLI::ignore_case));

    app.callback([&]() {
        if (fork_name) {
            revision = test::revision_map.at(*fork_name);
        }
    });

    app.add_option("--txn", txn_index, "Index of transaction to run");
    app.add_flag("--trace_calls", trace_calls, "Enable call tracing");
    app.add_option(
           "--blockchain-tests",
           blockchain_tests_path,
           "Path to blockchain tests, overrides the hard-coded tests path.")
        ->check(CLI::ExistingPath);
    app.add_option(
           "--transaction-tests",
           transaction_tests_path,
           "Path to transaction tests, overrides the hard-coded tests path.")
        ->check(CLI::ExistingPath);
    CLI::Option const *const record_exec_events =
        app.add_option(
               "--record-exec-events",
               record_exec_events_path,
               "Record execution events")
            ->expected(0, 1)
            ->type_name("<file-path> (leave empty for anonymous memfd)");
    app.add_option(
        "--sleep", sleep_seconds, "Sleep for the specified number of seconds");
    CLI11_PARSE(app, argc, argv);

    quill::start(true);
    quill::get_root_logger()->set_log_level(log_level);
#ifdef ENABLE_EVENT_TRACING
    event_tracer = quill::create_logger("event_trace", quill::null_handler());
#endif

    if (record_exec_events->count() > 0) {
        test::init_exec_event_recorder(record_exec_events_path);
    }

    std::this_thread::sleep_for(std::chrono::seconds{sleep_seconds});

    if (blockchain_tests_path || transaction_tests_path) {
        if (blockchain_tests_path) {
            test::register_blockchain_tests_path(
                *blockchain_tests_path, revision, trace_calls);
        }
        if (transaction_tests_path) {
            test::register_transaction_tests_path(
                *transaction_tests_path, revision);
        }
    }
    else {
        test::register_blockchain_tests(revision, trace_calls);
        test::register_transaction_tests(revision);
    }

    int return_code = RUN_ALL_TESTS();

    if (::testing::UnitTest::GetInstance()->test_to_run_count() == 0) {
        LOG_ERROR("No tests were run.");
        return_code = -1;
    }

    quill::flush();

    return return_code;
}
