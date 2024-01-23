#include <monad/core/bytes_fmt.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/mpt/trie.hpp>

#include <CLI/CLI.hpp>
#include <filesystem>
#include <memory>
#include <string>
#include <vector>

std::vector<std::filesystem::path>
get_ordered_files_from_dir(std::filesystem::path const &dir_name)
{
    std::vector<std::filesystem::path> file_names;
    try {
        for (auto const &entry :
             std::filesystem::directory_iterator(dir_name)) {
            if (std::filesystem::is_regular_file(entry.path())) {
                file_names.push_back(entry.path());
            }
        }
    }
    catch (std::filesystem::filesystem_error const &ex) {
        std::cerr << "Error accessing directory: " << ex.what() << std::endl;
    }

    std::sort(file_names.begin(), file_names.end());
    return file_names;
}

int run_command(std::string command)
{
    std::array<char, 128> buffer;
    std::string result;

    // Use popen to open a pipe and run the command
    FILE *pipe = popen(command.c_str(), "r");
    if (!pipe) {
        std::cerr << "Error opening pipe." << std::endl;
        return EXIT_FAILURE;
    }

    // Read the command output into the buffer
    while (fgets(buffer.data(), buffer.size(), pipe) != nullptr) {
        result += buffer.data();
    }

    // Close the pipe
    int status = pclose(pipe);

    if (status == 0) {
        std::cout << "Command executed successfully. Output:\n" << result;
    }
    else {
        std::cerr << "Error executing the command. Exit status: " << status
                  << std::endl;
    }

    return 0;
}

std::string unzip_json(std::filesystem::path &state_delta_file)
{
    auto begin_copy_n_unzip = std::chrono::steady_clock::now();
    // return a vector of json files
    std::string const dest_dir = "/home/vickychen/StateDeltaLog/";
    std::string const cp_file =
        "cp " + state_delta_file.string() + " " + dest_dir;
    // copy to dest_dir
    run_command(cp_file);
    // unsip from dest_dir
    std::string const gzip_filename =
        dest_dir + state_delta_file.filename().string();
    std::string const unzip = "gunzip " + gzip_filename;
    run_command(unzip);
    run_command("rm " + gzip_filename);
    auto end_copy_n_unzip = std::chrono::steady_clock::now();
    auto copy_n_unzip_secs =
        static_cast<double>(
            std::chrono::duration_cast<std::chrono::microseconds>(
                end_copy_n_unzip - begin_copy_n_unzip)
                .count()) /
        1000000.0;
    printf(
        "Time for cp + unzip %s: %f s\n",
        gzip_filename.c_str(),
        copy_n_unzip_secs);
    return gzip_filename.substr(0, gzip_filename.size() - 3);
}

int main(int argc, char *argv[])
{
    using namespace monad;

    bool append = false;
    bool compaction = false;
    std::filesystem::path snapshot_file;
    std::filesystem::path deltas_dir = "/home/jhunsaker/StateDeltaLog/";
    std::vector<std::filesystem::path> dbname_paths;
    unsigned sq_thread_cpu = 10;
    uint64_t snapshot_block_id = 14000000;

    CLI::App cli{"replay_ethereum_ondisk_triedb"};
    cli.add_flag("--append", append, "append at a specific block in db");
    cli.add_option(
        "--db-names", dbname_paths, "db file names, can have more than one");
    cli.add_option("--kcpu", sq_thread_cpu, "io_uring sq_thread_cpu");
    cli.add_option(
        "--snapshot-file", snapshot_file, "snapshot json file to load from");
    cli.add_option("--snapshot-block-num", snapshot_block_id);
    cli.add_option(
        "--deltas-dir",
        deltas_dir,
        "which stores zipped state delta json files to load from");
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

    // compact all data to slow ring
    // before this line we haven't inserted anything to aux.state_histories
    // we insert one entry after compact
    /* TEMPORARILY DISABLED: Write buffer not isolated from io state thus not
     * able to handle high performance io */
    // db->db().compact_most_aggresively_when_only_one_block(true);

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

    // MONAD_ASSERT(snapshot_block_id == db->block_id);
    db->db().init_state_info(snapshot_block_id);

    std::vector<std::filesystem::path> state_delta_files =
        get_ordered_files_from_dir(deltas_dir);
    for (auto &delta_file : state_delta_files) {
        std::string delta_json_filename = unzip_json(delta_file);
        // 1. parse delta
        std::ifstream delta_input(delta_json_filename);
        db->commit_multiple_blocks_from_json(delta_input);
        // 2. delete the json
        run_command("rm " + delta_json_filename);
    }
}
