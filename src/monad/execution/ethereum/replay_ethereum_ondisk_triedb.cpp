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
    unsigned sq_thread_cpu = 10;
    uint64_t snapshot_block_id = 140000000;

    CLI::App cli{"replay_ethereum_ondisk_triedb"};
    cli.add_flag("--append", append, "append at a specific block in db");
    cli.add_option(
        "--db-names", dbname_paths, "db file names, can have more than one");
    cli.add_option("--kcpu", sq_thread_cpu, "io_uring sq_thread_cpu");
    cli.add_option(
        "--snapshot-file", snapshot_file, "snapshot json file to load from");
    cli.add_option("--snapshot-block-num", snapshot_block_id);
    cli.add_option(
        "--deltas-files", snapshot_file, "state delta json file to load from");
    cli.add_flag("--compaction", compaction, "do compaction");
    cli.parse(argc, argv);

    if (dbname_paths.empty()) {
        dbname_paths.emplace_back("replay_test.db");
    }

    std::unique_ptr<db::TrieDb> db;
    auto begin_test = std::chrono::steady_clock::now();
    if (append) {
        db = std::make_unique<db::TrieDb>(
            mpt::DbOptions{
                .on_disk = true,
                .append = true,
                .compaction = compaction,
                .rd_buffers = 8192,
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
                .compaction = compaction,
                .rd_buffers = 8192,
                .wr_buffers = 128,
                .uring_entries = 128,
                .sq_thread_cpu = sq_thread_cpu,
                .dbname_paths = std::move(dbname_paths)},
            input,
            false /* DO NOT insert code*/,
            true /* per block, start from 0*/,
            250000000 /* batch size */,
            snapshot_block_id /* start block number */);
    }

    printf(
        "Total storage consumed: %f Gb\n",
        double(db->db().storage_bytes_used()) / 1024.0 / 1024.0 / 1024.0);

    // compact all data to slow ring
    // before this line we haven't inserted anything to aux.state_histories
    // we insert one entry after compact
    db->db().compact_most_aggresively_when_only_one_block(true);

    auto end_test = std::chrono::steady_clock::now();

    auto root_hash = fmt::format("14M state root: {}", db->state_root());
    std::cout << root_hash << std::endl;
    auto test_secs = static_cast<double>(
                         std::chrono::duration_cast<std::chrono::microseconds>(
                             end_test - begin_test)
                             .count()) /
                     1000000.0;
    printf(
        "\nTotal snapshot insert time: %f secs. Total storage consumed after "
        "compaction: %f Gb\n",
        test_secs,
        double(db->db().storage_bytes_used()) / 1024.0 / 1024.0 / 1024.0);

    // aux.state_histories.clear(); // insert the entry

    // TODO: upsert state deltas
    // 1. parse delta
    // 2. db->commit_from_json(state_deltas, code);
}
