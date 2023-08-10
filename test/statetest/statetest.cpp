// Modifications to the Original Code (or portions thereof):
// Monad: 2023
// - Fit naming and type conventions of Monad
// Original Code is licensed under the Apache 2.0 License
// monad: Fast Ethereum Virtual Machine implementation
// Copyright 2022 The monad Authors.
// SPDX-License-Identifier: Apache-2.0

#include "statetest.hpp"
#include <CLI/CLI.hpp>
#include <gtest/gtest.h>
#include <iostream>
#include <monad/logging/monad_log.hpp>

namespace
{

    using account_store_db_t = monad::db::InMemoryTrieDB;
    using code_db_t = std::unordered_map<monad::bytes32_t, monad::byte_string>;
    class StateTest : public testing::Test
    {
        fs::path m_json_test_file;
        evmc::VM &m_vm;
        std::string suite_name;
        std::string test_name;
        std::string file_name;

    public:
        explicit StateTest(
            fs::path json_test_file, evmc::VM &vm, std::string suite_name,
            std::string test_name, std::string file_name) noexcept
            : m_json_test_file{std::move(json_test_file)}
            , m_vm{vm}
            , suite_name{suite_name}
            , test_name{test_name}
            , file_name{file_name}
        {
        }

        void TestBody() final
        {
            try {
                std::ifstream f{m_json_test_file};

                monad::db::BlockDb blocks{"some_path"};
                account_store_db_t db{};
                monad::state::AccountState accounts{db};
                monad::state::ValueState values{db};
                code_db_t code_db{};
                monad::state::CodeState codes{code_db};
                monad::state::State state{accounts, values, codes, blocks, db};
                using change_set_t =
                    decltype(std::declval<monad::test::state_t>()
                                 .get_new_changeset(0));

                auto change_set = state.get_new_changeset(0);
                monad::test::StateTransitionTest<change_set_t>
                    state_transition_test{.pre_state_ = change_set};
                monad::test::load_state_test<change_set_t>(
                    state_transition_test, f, suite_name, test_name, file_name);

                monad::test::run_state_test(state_transition_test, m_vm);
            }
            catch (std::out_of_range &e) {
                std::cout << "a" << std::endl;
            }
            catch (std::exception const &e) {
                std::cout << "b" << std::endl;
            }
            catch (...) {
                std::cout << "c" << std::endl;
            }
        }
    };

    void register_test(
        std::string const &suite_name, fs::path const &file, evmc::VM &vm)
    {
        testing::RegisterTest(
            suite_name.c_str(),
            file.stem().string().c_str(),
            nullptr,
            nullptr,
            file.string().c_str(),
            0,
            [file, &vm, suite_name]() -> testing::Test * {
                return new StateTest(
                    file, vm, suite_name, file.stem().string(), file.string());
            });
    }

    void register_test_files(fs::path const &root, evmc::VM &vm)
    {
        if (is_directory(root)) {
            std::vector<fs::path> test_files;
            std::copy_if(
                fs::recursive_directory_iterator{root},
                fs::recursive_directory_iterator{},
                std::back_inserter(test_files),
                [](fs::directory_entry const &entry) {
                    return entry.is_regular_file() &&
                           entry.path().extension() == ".json";
                });
            std::sort(test_files.begin(), test_files.end());

            for (auto const &p : test_files)
                register_test(
                    fs::relative(p, root).parent_path().string(), p, vm);
        }
        else // Treat as a file.
        {
            register_test(root.parent_path().string(), root, vm);
        }
    }
} // namespace

int main(int argc, char *argv[])
{

    [[maybe_unused]] auto *compatibility_logger =
        monad::log::logger_t::create_logger("compatibility_logger");
    [[maybe_unused]] auto *trie_db_logger =
        monad::log::logger_t::create_logger("trie_db_logger");
    trie_db_logger->set_log_level(quill::LogLevel::Debug);
    [[maybe_unused]] auto *change_set_logger =
        monad::log::logger_t::create_logger("change_set_logger");
    change_set_logger->set_log_level(quill::LogLevel::Debug);
    [[maybe_unused]] auto *evmone_baseline_interpreter_logger =
        monad::log::logger_t::create_logger(
            "evmone_baseline_interpreter_logger");
    evmone_baseline_interpreter_logger->set_log_level(quill::LogLevel::Debug);
    // monad::log::logger_t::start();

    // The default test filter. To enable all tests use `--gtest_filter=*`.
    testing::FLAGS_gtest_filter =
        "-"
        // Slow tests:
        "stCreateTest.CreateOOGafterMaxCodesize:" // pass
        "stQuadraticComplexityTest.Call50000_sha256:" // pass
        "stTimeConsuming.static_Call50000_sha256:" // pass
        "stTimeConsuming.CALLBlake2f_MaxRounds:" // pass
        "VMTests/vmPerformance.*:" // pass
        ;

    //    try {
    testing::InitGoogleTest(&argc, argv); // Process GoogleTest flags.

    CLI::App app{"monad state test runner"};

    std::vector<std::string> paths;
    app.add_option("--path", paths, "Path to test file or directory")
        ->required()
        ->check(CLI::ExistingPath);

    bool trace_flag = false;
    app.add_flag("--trace", trace_flag, "Enable EVM tracing");

    CLI11_PARSE(app, argc, argv);

    //        evmc::VM vm{evmc_create_evmone(), {{"O", "0"}}};
    evmc::VM vm{};

    if (trace_flag)
        vm.set_option("trace", "1");

    for (auto const &p : paths)
        register_test_files(p, vm);

    return RUN_ALL_TESTS();
    //    }
    //    catch (std::exception const &ex) {
    //        std::cerr << ex.what() << "\n";
    //        return -1;
    //    }
}
