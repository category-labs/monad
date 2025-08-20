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

#include <blockchain_test.hpp>
#include <ethereum_test.hpp>
#include <event.hpp>
#include <monad/test/config.hpp>
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
    bool trace_calls = false;
    bool record_exec_events = false;

    CLI::App app{"monad ethereum tests runner"};
    app.add_option("--log_level", log_level, "Logging level")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    app.add_option("--fork", revision, "Fork to run unit tests for")
        ->transform(
            CLI::CheckedTransformer(test::revision_map, CLI::ignore_case));
    app.add_option("--txn", txn_index, "Index of transaction to run");
    app.add_flag("--trace_calls", trace_calls, "Enable call tracing");
    app.add_flag(
        "--record-exec-events", record_exec_events, "Record execution events");
    CLI11_PARSE(app, argc, argv);

    quill::start(true);
    quill::get_root_logger()->set_log_level(log_level);
#ifdef ENABLE_EVENT_TRACING
    event_tracer = quill::create_logger("event_trace", quill::null_handler());
#endif

    test::register_blockchain_tests(revision, trace_calls);
    test::register_transaction_tests(revision);

    int return_code = RUN_ALL_TESTS();

    if (::testing::UnitTest::GetInstance()->test_to_run_count() == 0) {
        LOG_ERROR("No tests were run.");
        return_code = -1;
    }

    quill::flush();

    return return_code;
}
