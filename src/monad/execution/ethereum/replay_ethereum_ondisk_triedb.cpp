#include <monad/core/bytes_fmt.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/mpt/trie.hpp>

#include <CLI/CLI.hpp>
#include <filesystem>
#include <memory>
#include <vector>

int main(int argc, char *argv[])
{
    using namespace monad;

    bool append = false;
    bool compaction = false;
    std::filesystem::path snapshot_file;
    std::vector<std::filesystem::path> deltas_files;
    std::vector<std::filesystem::path> dbname_paths;
    unsigned sq_thread_cpu = 15;

    CLI::App cli{"replay_ethereum_ondisk_triedb"};
    cli.add_flag("--append", append, "append at a specific block in db");
    cli.add_option(
        "--db-names", dbname_paths, "db file names, can have more than one");
    cli.add_option("--kcpu", sq_thread_cpu, "io_uring sq_thread_cpu");
    cli.add_option(
        "--snapshot-file", snapshot_file, "snapshot json file to load from");
    cli.add_option(
        "--deltas-files", snapshot_file, "state delta json file to load from");
    cli.add_flag("--compaction", compaction, "do compaction");
    cli.parse(argc, argv);

    if (dbname_paths.empty()) {
        dbname_paths.emplace_back("test.db");
    }

    std::unique_ptr<db::TrieDb> db;
    if (append) {
        db = std::make_unique<db::TrieDb>(
            mpt::DbOptions{
                .on_disk = true,
                .append = true,
                .rd_buffers = 8192 * 32,
                .wr_buffers = 128,
                .uring_entries = 128,
                .sq_thread_cpu = sq_thread_cpu,
                .dbname_paths = std::move(dbname_paths)},
            false /* DO NOT insert code*/,
            true /* per block, start from 0*/);
    }
    else {
        MONAD_ASSERT(!snapshot_file.empty());
        std::ifstream input{snapshot_file};
        db = std::make_unique<db::TrieDb>(
            mpt::DbOptions{
                .on_disk = true,
                .append = false,
                .rd_buffers = 8192 * 32,
                .wr_buffers = 128,
                .uring_entries = 128,
                .sq_thread_cpu = sq_thread_cpu,
                .dbname_paths = std::move(dbname_paths)},
            input,
            false /* DO NOT insert code*/,
            true /* per block, start from 0*/,
            1000000 /* batch size */,
            14000000 /* start block number */);
    }
    auto bytes = fmt::format("14M state root: {}", db->state_root());
    std::cout << bytes << std::endl;

    // TODO: upsert state deltas
    // 1. parse delta
    // 2. db->commit_from_json(state_deltas, code);
}
