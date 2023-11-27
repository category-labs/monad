#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/permission.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/replay_block_db.hpp>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <cstdint>
#include <filesystem>
#include <iostream>
#include <optional>
#include <ostream>
#include <vector>

MONAD_NAMESPACE_BEGIN

using receiptCollector = std::vector<std::vector<Receipt>>;
using eth_start_fork = fork_traits::frontier;

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;

    CLI::App cli{"replay_ethereum"};

    std::filesystem::path block_db_path{};
    std::filesystem::path state_db_path{};
    std::filesystem::path genesis_file_path{};
    uint64_t block_history_size = 1u;
    uint64_t checkpoint_frequency = 1000u;
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
        "--block_history_size",
        block_history_size,
        "size of state_db block history");
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

    auto const start_time = std::chrono::steady_clock::now();

    using db_t = db::RocksTrieDB;

    BlockDb block_db(block_db_path);
    db_t db{db::Writable{}, state_db_path, std::nullopt, block_history_size};

    block_num_t start_block_number = db.starting_block_number;

    quill::get_root_logger()->set_log_level(log_level);

    LOG_INFO(
        "Running with block_db = {}, state_db = {}, block_history_size = {}, "
        "(inferred) start_block_number = {}, finish block number = {}",
        block_db_path,
        state_db_path,
        block_history_size,
        start_block_number,
        finish_block_number);

    if (start_block_number == 0) {
        MONAD_DEBUG_ASSERT(*has_genesis_file);
        read_and_verify_genesis(block_db, db, genesis_file_path);
        start_block_number = 1u;
    }

    ReplayFromBlockDb<db_t> replay_eth;

    [[maybe_unused]] auto result = replay_eth.run<eth_start_fork>(
        db,
        checkpoint_frequency,
        block_db,
        start_block_number,
        finish_block_number);

    auto const finished_time = std::chrono::steady_clock::now();
    auto const elapsed_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            finished_time - start_time);

    LOG_INFO(
        "Finish running, status = {}, finish(stopped) block number = {}, "
        "number of blocks run = {}, time_elapsed = {}",
        static_cast<int>(result.status),
        result.block_number,
        result.block_number - start_block_number + 1,
        elapsed_ms);

    return 0;
}
