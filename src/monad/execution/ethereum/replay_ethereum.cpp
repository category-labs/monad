#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/receipt.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/db_cache.hpp>
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

#include <sys/sysinfo.h>

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
    bool on_disk = false;
    bool compaction = false;
    unsigned nthreads = 4;
    unsigned nfibers = 4;
    auto sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    std::vector<std::filesystem::path> dbname_paths;
    int64_t file_size_db = 512; // 512GB

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
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_flag("--on_disk", on_disk, "config TrieDb to be on disk");
    cli.add_flag("--compaction", compaction, "do compaction");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "io_uring sq_thread_cpu field in io_uring_params");
    cli.add_option(
        "--dbname_paths",
        dbname_paths,
        "a list of db paths separated by comma, can config storage pool "
        "with 1 or more files/devices, will config on_disk triedb with "
        "anonymous inode if empty");
    cli.add_option(
        "--file_size_db",
        file_size_db,
        "size of each db file, only apply to newly created files but not "
        "existing files or raw blkdev");

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
    auto const config = on_disk ? std::make_optional(mpt::OnDiskDbConfig{
                                      .append = false,
                                      .compaction = compaction,
                                      .rd_buffers = 8192,
                                      .wr_buffers = 32,
                                      .uring_entries = 128,
                                      .sq_thread_cpu = sq_thread_cpu,
                                      .dbname_paths = dbname_paths,
                                      .file_size_db = file_size_db})
                                : std::nullopt;
    auto db = [&] -> db::TrieDb {
        if (start_block_number == 0) {
            return db::TrieDb{config};
        }
        auto const dir = state_db_path / std::to_string(start_block_number - 1);
        if (std::filesystem::exists(dir / "accounts")) {
            MONAD_ASSERT(std::filesystem::exists(dir / "code"));
            LOG_INFO("Loading from binary checkpoint in {}", dir);
            std::ifstream accounts(dir / "accounts");
            std::ifstream code(dir / "code");
            return db::TrieDb{config, accounts, code};
        }
        MONAD_ASSERT(std::filesystem::exists(dir / "state.json"));
        LOG_INFO("Loading from json checkpoint in {}", dir);
        std::ifstream ifile_stream(dir / "state.json");
        return db::TrieDb{config, ifile_stream};
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

    fiber::PriorityPool priority_pool{nthreads, nfibers};

    ReplayFromBlockDb replay_eth;

    auto const start_time = std::chrono::steady_clock::now();

    DbCache db_cache{db};

    auto result = replay_eth.run<eth_start_fork>(
        db_cache,
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
