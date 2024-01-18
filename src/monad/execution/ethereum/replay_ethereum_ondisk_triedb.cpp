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
    std::filesystem::path dbname_path = "replay_test.db";
    unsigned sq_thread_cpu = 15;

    CLI::App cli{"replay_ethereum_ondisk_triedb"};
    cli.add_flag("--append", append, "append at a specific block in db");
    cli.add_option("--db-name", dbname_path, "db file name");
    cli.add_option("--kcpu", sq_thread_cpu, "io_uring sq_thread_cpu");
    cli.add_option(
        "--snapshot-file", snapshot_file, "snapshot json file to load from");
    cli.add_option(
        "--deltas-files", snapshot_file, "state delta json file to load from");
    cli.add_flag("--compaction", compaction, "do compaction");
    cli.parse(argc, argv);

    std::unique_ptr<db::TrieDb> db;
    if (append) {
        db = std::make_unique<db::TrieDb>(mpt::DbOptions{
            .on_disk = true,
            .append = true,
            .rd_buffers = 8192 * 32,
            .wr_buffers = 128,
            .uring_entries = 128,
            .sq_thread_cpu = sq_thread_cpu,
            .dbname = dbname_path});
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
                .dbname = dbname_path},
            input);
    }
    auto bytes = fmt::format("14M state root: {}", db->state_root());
    std::cout << bytes << std::endl;
    // TODO: upsert state deltas
}
