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
        if (MONAD_UNLIKELY(block_number_int % 1 == 0)) {
            LOG_INFO(
                "Successfully processed up to block: {}", block_number_int);
        }
    }

    return true;
}

std::vector<std::pair<monad::StateDeltas, monad::Code>>
get_deltas_from_file(std::filesystem::path const &file_path)
{
    std::vector<std::pair<monad::StateDeltas, monad::Code>> state_deltas_vector;
    MONAD_ASSERT(std::filesystem::exists(file_path));
    std::ifstream ifile(file_path, std::ifstream::binary);
    nlohmann::json state_deltas_vector_json;
    ifile >> state_deltas_vector_json;

    for (auto const &[block_number, state_deltas_json] :
         state_deltas_vector_json.items()) {
        monad::StateDeltas state_deltas;
        monad::Code code_deltas;

        for (auto const &[addr, acct] :
             state_deltas_json["StateDelta"].items()) {

            auto const address = evmc::from_hex<monad::Address>(addr).value();
            auto const code =
                evmc::from_hex(acct.at("code_hash").get<std::string>()).value();
            Account account{
                .balance = intx::from_string<uint256_t>(acct.at("balance")),
                .nonce = std::stoull(
                    acct.at("nonce").get<std::string>(), nullptr, 16),
                .incarnation = std::stoull(
                    acct.at("incarnation").get<std::string>(), nullptr, 16)};
            std::memcpy(account.code_hash.bytes, code.data(), 32);

            StateDelta state_delta{.account = {Account{}, std::nullopt}};

            if (MONAD_LIKELY(!is_empty(account))) {
                state_delta.account.second = account;
            }

            // storage
            for (auto const &[key, value] : acct["storage"].items()) {
                bytes32_t storage_key;
                bytes32_t storage_value;
                bytes32_t fake_original_storage_value;
                std::memcpy(
                    storage_key.bytes, evmc::from_hex(key).value().data(), 32);
                std::memcpy(
                    storage_value.bytes,
                    evmc::from_hex(value.get<std::string>()).value().data(),
                    32);

                fake_original_storage_value =
                    storage_value == bytes32_t{} ? NULL_HASH : bytes32_t{};

                state_delta.storage.emplace(std::make_pair(
                    storage_key,
                    std::make_pair(
                        fake_original_storage_value, storage_value)));
            }

            state_deltas.emplace(address, state_delta);
        }

        // We don't care about code delta, just leave it empty for now

        state_deltas_vector.emplace_back(
            std::make_pair(state_deltas, code_deltas));
    }

    return state_deltas_vector;
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

    std::filesystem::path state_db_path{};
    std::filesystem::path state_delta_path{};
    std::filesystem::path block_db_path{};

    quill::start(true);

    auto log_level = quill::LogLevel::Info;
    cli.add_option("--state_db", state_db_path, "state_db directory")
        ->required();
    cli.add_option("--state_delta", state_delta_path, "state delta directory")
        ->required();
    cli.add_option("--block_db", block_db_path, "block_db directory")
        ->required();
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

    auto const finished_loading_time = std::chrono::steady_clock::now();
    auto const elapsed_loading_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            finished_loading_time - start_time);
    LOG_INFO(
        "Finished initializing db at block = {}, time elapsed = {}",
        start_block_number,
        elapsed_loading_ms);

    quill::get_root_logger()->set_log_level(log_level);

    auto const files = get_ordered_files_from_dir(state_delta_path);

    // block_db stuff (temp)
    BlockDb block_db{block_db_path};

    for (auto const &file : files) {
        if (!process_file_and_commit_to_db(db, block_db, file)) {
            return 1;
        }
    }

    return 0;
}
