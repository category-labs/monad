#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/replay_block_db.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>

MONAD_NAMESPACE_BEGIN

using eth_start_fork = fork_traits::frontier;

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;

    CLI::App cli{"replay_ethereum"};

    std::filesystem::path block_db_path{};
    std::filesystem::path state_db_path{};
    std::filesystem::path genesis_file_path{};
    std::optional<uint64_t> checkpoint_frequency = std::nullopt;
    std::optional<block_num_t> finish_block_number = std::nullopt;

    quill::start(true);

    auto log_level = quill::LogLevel::Info;
    cli.add_option("--block_db", block_db_path, "block_db directory")
        ->required();
    cli.add_option("--state_db", state_db_path, "state_db directory")
        ->required();
    auto *has_genesis_file = cli.add_option(
        "--genesis_file", genesis_file_path, "genesis file directory");
    cli.add_option(
        "--checkpoint_frequency",
        checkpoint_frequency,
        "state db checkpointing frequency");
    cli.add_option(
        "--finish", finish_block_number, "1 pass the last executed block");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));

    try {
        cli.parse(argc, argv);
    }
    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
        return cli.exit(e);
    }

    auto block_db = BlockDb(block_db_path);

    auto const load_start_time = std::chrono::steady_clock::now();
    auto start_block_number = db::auto_detect_start_block_number(state_db_path);
    auto const opts = mpt::DbOptions{.on_disk = false};

    auto db = [&] -> db::TrieDb {
        if (start_block_number == 0) {
            return db::TrieDb{opts};
        }

        auto const dir = state_db_path / std::to_string(start_block_number - 1);
        if (std::filesystem::exists(dir / "accounts")) {
            MONAD_ASSERT(std::filesystem::exists(dir / "code"));
            LOG_INFO("Loading from binary checkpoint in {}", dir);
            std::ifstream accounts(dir / "accounts");
            std::ifstream code(dir / "code");
            return db::TrieDb{opts, accounts, code};
        }
        MONAD_ASSERT(std::filesystem::exists(dir / "state.json"));
        LOG_INFO("Loading from json checkpoint in {}", dir);
        std::ifstream ifile_stream(dir / "state.json");
        return db::TrieDb{opts, ifile_stream};
    }();

    if (start_block_number == 0) {
        MONAD_ASSERT(*has_genesis_file);
        read_and_verify_genesis(block_db, db, genesis_file_path);
        start_block_number = 1;
    }

    auto const load_finish_time = std::chrono::steady_clock::now();
    auto const load_elapsed =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            load_finish_time - load_start_time);
    LOG_INFO(
        "Finished initializing db at block = {}, time elapsed = {}",
        start_block_number,
        load_elapsed);

    quill::get_root_logger()->set_log_level(log_level);

    LOG_INFO(
        "Running with block_db = {}, state_db = {}, "
        "(inferred) start_block_number = {}, finish block number = {}",
        block_db_path,
        state_db_path,
        start_block_number,
        finish_block_number);

    fiber::PriorityPool priority_pool{4, 4};

    ReplayFromBlockDb<decltype(db)> replay_eth;

    auto const start_time = std::chrono::steady_clock::now();

    [[maybe_unused]] auto result = replay_eth.run<eth_start_fork>(
        db,
        block_db,
        priority_pool,
        state_db_path,
        checkpoint_frequency,
        start_block_number,
        finish_block_number);

    auto const finish_time = std::chrono::steady_clock::now();
    auto const elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        finish_time - start_time);

    LOG_INFO(
        "Finish running, status = {}, finish(stopped) block number = {}, "
        "number of blocks run = {}, time_elapsed = {}, num transactions = {}, "
        "tps = {}",
        static_cast<int>(result.status),
        result.block_number,
        result.block_number - start_block_number + 1,
        elapsed,
        replay_eth.n_transactions,
        replay_eth.n_transactions /
            std::max(1UL, static_cast<uint64_t>(elapsed.count())));

    return 0;
}
