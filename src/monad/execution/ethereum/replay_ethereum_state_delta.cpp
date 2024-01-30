#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/replay_block_db.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <CLI/CLI.hpp>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <vector>

using namespace monad;

bool verify_root_hash(
    BlockDb &block_db, bytes32_t state_root_hash, uint64_t const block_number)
{
    Block block{};
    block_db.get(block_number, block);

    return block.header.state_root == state_root_hash;
}

bool process_file_and_commit_to_db(
    db::TrieDb &trie_db, BlockDb &block_db,
    std::filesystem::path const &file_path)
{
    MONAD_ASSERT(std::filesystem::exists(file_path));
    std::ifstream ifile(file_path, std::ifstream::binary);
    nlohmann::json state_deltas_vector_json;
    ifile >> state_deltas_vector_json;

    for (auto const &[block_number, state_deltas_json] :
         state_deltas_vector_json.items()) {
        trie_db.commit(state_deltas_json);

        block_num_t block_number_int = std::stoull(block_number);
        if (MONAD_UNLIKELY(!verify_root_hash(
                block_db, trie_db.state_root(), block_number_int))) {
            LOG_ERROR("State Root Mismatch at block: {}", block_number_int);
            return false;
        }
        if (MONAD_UNLIKELY(block_number_int % 1000 == 0)) {
            LOG_INFO(
                "Successfully processed up to block: {}", block_number_int);
        }
    }

    return true;
}

int run_command(std::string command)
{
    LOG_INFO("bash: {}", command);
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

std::string unzip_json(std::filesystem::path const &state_delta_file)
{
    auto begin_copy_n_unzip = std::chrono::steady_clock::now();
    // return a vector of json files
    std::string const dest_dir = "/home/vickychen/StateDeltaLog/";
    std::string const cp_file =
        "cp " + state_delta_file.string() + " " + dest_dir;
    // copy to dest_dir
    run_command(cp_file);
    // unsip from dest_dir
    std::string const gzip_filename = dest_dir / state_delta_file.filename();
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

int main(int argc, char *argv[])
{
    using namespace monad;

    CLI::App cli{"replay_ethereum_state_delta"};

    std::filesystem::path block_db_path{};
    std::filesystem::path state_db_path{};
    std::filesystem::path genesis_file_path{};
    std::filesystem::path state_delta_path{"/home/jhunsaker/StateDeltaLog/"};
    std::optional<uint64_t> checkpoint_frequency = std::nullopt;
    std::optional<block_num_t> finish_block_number = std::nullopt;
    bool in_memory = false;
    std::optional<uint64_t> block_id_continue = std::nullopt;
    bool compaction = false;
    unsigned nthreads = 1;
    unsigned sq_thread_cpu = 15;
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
    cli.add_option("--nthreads", nthreads, "number of threads and fibers");
    cli.add_flag(
        "--in_memory", in_memory, "config TrieDb to in memory or on-disk");
    cli.add_option(
        "--block_id_continue",
        block_id_continue,
        "block id to continue running onto an existing on disk TrieDb "
        "instance");
    cli.add_flag("--compaction", compaction, "do compaction");
    cli.add_option("--sq_thread_cpu", sq_thread_cpu, "io_uring sq_thread_cpu");
    cli.add_option(
        "--dbname_paths",
        dbname_paths,
        "db file names, can have more than one");
    cli.add_option(
        "--file_size_db",
        file_size_db,
        "size to create file to if not already exist, only apply to file "
        "not blkdev");
    cli.add_option("--state_delta", state_delta_path, "state delta directory")
        ->required();

    try {
        cli.parse(argc, argv);
    }
    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
        return cli.exit(e);
    }

    auto block_db = BlockDb(block_db_path);

    auto const load_start_time = std::chrono::steady_clock::now();
    bool const append = block_id_continue.has_value() && !in_memory;
    auto start_block_number =
        append ? block_id_continue.value()
               : db::auto_detect_start_block_number(state_db_path);

    if (dbname_paths.empty()) {
        dbname_paths.emplace_back("replay_test.db");
    }
    mpt::OnDiskDbConfig ondisk_config{
        .append = append,
        .compaction = compaction,
        .rd_buffers = 8192,
        .wr_buffers = 32,
        .uring_entries = 128,
        .sq_thread_cpu = sq_thread_cpu,
        .start_block_id = block_id_continue,
        .dbname_paths = dbname_paths};
    auto db = [&] -> db::TrieDb {
        if (start_block_number == 0 || append) {
            return in_memory ? db::TrieDb{std::nullopt}
                             : db::TrieDb{ondisk_config};
        }
        auto const dir = state_db_path / std::to_string(start_block_number - 1);
        if (std::filesystem::exists(dir / "accounts")) {
            MONAD_ASSERT(std::filesystem::exists(dir / "code"));
            LOG_INFO("Loading from binary checkpoint in {}", dir);
            std::ifstream accounts(dir / "accounts");
            std::ifstream code(dir / "code");
            ondisk_config.append = false;
            ondisk_config.start_block_id = start_block_number;
            // in memory should always insert to the same block id
            return in_memory ? db::TrieDb{std::nullopt, accounts, code}
                             : db::TrieDb{ondisk_config, accounts, code};
        }
        MONAD_ASSERT(std::filesystem::exists(dir / "state.json"));
        LOG_INFO("Loading from json checkpoint in {}", dir);
        std::ifstream ifile_stream(dir / "state.json");
        return in_memory ? db::TrieDb{std::nullopt, ifile_stream}
                         : db::TrieDb{ondisk_config, ifile_stream};
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

    auto const state_delta_files = get_ordered_files_from_dir(state_delta_path);

    LOG_INFO(
        "Replaying TrieDb with StateDeltas (inferred) start_block_number = {}, "
        "finish block number = {}",
        start_block_number,
        finish_block_number);

    for (auto &delta_file : state_delta_files) {
        std::string delta_json_filename = unzip_json(delta_file);
        if (!process_file_and_commit_to_db(db, block_db, delta_file)) {
            return 1;
        }
        // 2. delete the json
        run_command("rm " + delta_json_filename);
    }

    // TODO end log

    return 0;
}
