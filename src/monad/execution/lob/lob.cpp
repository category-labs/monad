#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/fmt/receipt_fmt.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <optional>
#include <random>
#include <sstream>

#include <sys/sysinfo.h>

MONAD_NAMESPACE_BEGIN

using current_fork = fork_traits::shanghai;

static constexpr auto beneficiary =
    0x388C818CA8B9251b393131C08a736A67ccB19297_address;
static constexpr uint256_t base_fee_per_gas = 1'000'000'000u;
std::string global_value;

std::random_device rd;
std::mt19937 gen(rd());
std::uniform_int_distribution<uint64_t>
    distrib(0, std::numeric_limits<uint64_t>::max());

std::optional<byte_string_view>
get(std::filesystem::path const &path, bool const setup, uint64_t const num)
{
    std::string filename;

    if (MONAD_UNLIKELY(setup)) {
        filename = "setup.bin";
    }
    else {
        filename = "transaction-" + std::to_string(num) + ".bin";
    }
    std::ifstream in{path / filename, std::ios::in | std::ios::binary};
    if (!in) {
        return std::nullopt;
    }

    in.seekg(0, std::ios::end);
    auto const pos = in.tellg();
    MONAD_ASSERT(pos >= 0);
    global_value.resize(static_cast<size_t>(pos));
    in.seekg(0, std::ios::beg);
    in.read(
        &global_value[0], static_cast<std::streamsize>(global_value.size()));
    in.close();

    auto const view = to_byte_string_view(global_value);

    return view;
}

std::vector<Address> get_addresses_from_file(std::filesystem::path const &path)
{
    std::vector<Address> addresses;
    std::string address_file = path / "accounts.txt";
    std::ifstream in(address_file);
    MONAD_ASSERT(in.is_open());

    std::string line;
    std::string address;
    while (std::getline(in, line)) {
        std::stringstream ss(line);
        std::getline(ss, address, ',');
        std::getline(ss, address);

        address = address.substr(2, 42);
        Address formatted_address =
            evmc::from_hex<monad::Address>(address).value();
        addresses.emplace_back(std::move(formatted_address));
    }

    return addresses;
}

Block make_block(byte_string_view &encoded_txns, block_num_t const block_num)
{
    Block block;
    BlockHeader block_header;
    block_header.beneficiary = beneficiary;
    block_header.base_fee_per_gas = std::make_optional(base_fee_per_gas);
    block_header.number = block_num;

    auto txns = rlp::decode_transaction_vector(encoded_txns);
    if (txns.has_error()) {
        LOG_INFO("Decode error: {}", txns.assume_error().value());
    }
    MONAD_ASSERT(!txns.has_error());

    block.header = block_header;
    block.transactions = std::move(txns.value());

    return block;
}

Address generate_random_address()
{
    return Address(distrib(gen));
}

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;

    CLI::App cli{"lob"};

    std::filesystem::path block_db_path{};
    std::filesystem::path state_db_path{};
    std::optional<uint64_t> block_id_continue = std::nullopt;
    uint64_t finish_batch = 1500;

    bool compaction = false;
    unsigned nthreads = 4;
    unsigned nfibers = 4;
    auto sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    std::vector<std::filesystem::path> dbname_paths;
    std::filesystem::path load_snapshot{};

    quill::start(true);

    auto log_level = quill::LogLevel::Info;
    cli.add_option("--block_db", block_db_path, "block_db directory")
        ->required();
    cli.add_option(
        "--finish_batch", finish_batch, "Last batch of txn to execute");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_flag("--compaction", compaction, "do compaction");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "io_uring sq_thread_cpu field in io_uring_params");
    auto const on_disk_option = cli.add_option(
        "--db",
        dbname_paths,
        "A comma-separated list of previously created database paths. You can "
        "configure the storage pool with one or more files/devices. If no "
        "value is passed, the replay will run with an in-memory triedb");
    auto const snapshot_option = cli.add_option(
        "--load_snapshot", load_snapshot, "snapshot file path to load db from");
    auto const resume_option = cli.add_option(
        "--block_id_continue",
        block_id_continue,
        "block id to continue running from an existing on disk TrieDb "
        "instance");

    snapshot_option->excludes(resume_option);
    resume_option->needs(on_disk_option);

    try {
        cli.parse(argc, argv);
    }
    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
        return cli.exit(e);
    }
    quill::get_root_logger()->set_log_level(log_level);

    bool const on_disk = !dbname_paths.empty();
    auto const config = on_disk ? std::make_optional(mpt::OnDiskDbConfig{
                                      .append = true, // always open existing
                                      .compaction = compaction,
                                      .rd_buffers = 8192,
                                      .wr_buffers = 32,
                                      .uring_entries = 128,
                                      .sq_thread_cpu = sq_thread_cpu,
                                      .start_block_id = block_id_continue,
                                      .dbname_paths = dbname_paths})
                                : std::nullopt;

    uint64_t init_block_number = 0;
    auto db = [&] -> db::TrieDb {
        if (load_snapshot.empty()) {
            return db::TrieDb{config};
        }
        MONAD_ASSERT(!block_id_continue.has_value());
        namespace fs = std::filesystem;
        if (!(fs::is_directory(load_snapshot) &&
              (fs::exists(load_snapshot / "state.json") ||
               (fs::exists(load_snapshot / "accounts") &&
                fs::exists(load_snapshot / "code"))))) {
            throw std::runtime_error(
                "Invalid snapshot folder provided. Please ensure that the "
                "directory you pass contains the block number of the snapshot "
                "in its path and includes either files 'accounts' and 'code', "
                "or 'state.json'.");
        }
        init_block_number = std::stoul(load_snapshot.stem());
        if (fs::exists(load_snapshot / "accounts")) {
            MONAD_ASSERT(fs::exists(load_snapshot / "code"));
            LOG_INFO("Loading from binary checkpoint in {}", load_snapshot);
            std::ifstream accounts(load_snapshot / "accounts");
            std::ifstream code(load_snapshot / "code");
            return db::TrieDb{config, accounts, code, init_block_number};
        }
        MONAD_ASSERT(fs::exists(load_snapshot / "state.json"));
        LOG_INFO("Loading from json checkpoint in {}", load_snapshot);
        std::ifstream ifile_stream(load_snapshot / "state.json");
        return db::TrieDb{config, ifile_stream, init_block_number};
    }();

    init_block_number = db.current_block_number();

    LOG_INFO(
        "Running with block_db = {}, finish batch = {}",
        block_db_path,
        finish_batch);

    fiber::PriorityPool priority_pool{nthreads, nfibers};

    auto const addresses = get_addresses_from_file(block_db_path);

    // Deposit balance
    {
        BlockState block_state{db};
        State state{block_state};
        for (auto const &address : addresses) {
            state.add_to_balance(
                address, base_fee_per_gas * base_fee_per_gas * 10'000u);
        }
        MONAD_ASSERT(block_state.can_merge(state));
        block_state.merge(state);
        LOG_DEBUG("Commiting deposit balance txns");
        block_state.commit();
    }

    LOG_INFO("Finished adding balance to {} active accounts", addresses.size());

    // execute setup txns
    {
        auto block_byte_string = get(block_db_path, /*setup*/ true, 0);
        MONAD_ASSERT(block_byte_string);
        Block setup_block =
            make_block(block_byte_string.value(), init_block_number + 1);
        BlockHashBuffer buffer;
        BlockState block_state{db};
        uint64_t cumulative_gas_used = 0u;
        auto const receipts = execute_block_no_post_validate<EVMC_SHANGHAI>(
            setup_block,
            buffer,
            priority_pool,
            block_state,
            cumulative_gas_used);
        block_state.commit();
        LOG_DEBUG("Size of receipt: {}", receipts.value().size());
    }

    LOG_INFO("Finished executing setup transactions");
    auto const start_time = std::chrono::steady_clock::now();

    // execute other txns

    for (uint64_t i = 0; i < std::min(finish_batch, uint64_t{1500}); ++i) {
        auto block_byte_string = get(block_db_path, /*setup*/ false, i);
        MONAD_ASSERT(block_byte_string);
        Block setup_block =
            make_block(block_byte_string.value(), init_block_number + 2 + i);
        BlockHashBuffer buffer;
        BlockState block_state{db};
        uint64_t cumulative_gas_used = 0u;
        auto const receipts = execute_block_no_post_validate<EVMC_SHANGHAI>(
            setup_block,
            buffer,
            priority_pool,
            block_state,
            cumulative_gas_used);
        block_state.commit();
        LOG_INFO("At file {}", i);

        for (auto const &receipt : receipts.value()) {
            if (receipt.status != 1) {
                LOG_ERROR("Error receipt: {}", receipt);
            }
        }
    }

    auto const finish_time = std::chrono::steady_clock::now();
    auto const time_elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        finish_time - start_time);

    // auto const num = db.count();

    LOG_INFO(
        "Finished running, num files = {}, num transactions = {}k, time "
        "elasped = {}, tps = {}",
        std::min(finish_batch, uint64_t{1500}),
        std::min(finish_batch, uint64_t{1500}),
        time_elapsed,
        finish_batch * 1000 /
            std::max(1UL, static_cast<uint64_t>(time_elapsed.count())));

    // LOG_INFO(
    //     "Number of accounts = {}, number of storage = {}",
    //     num.first,
    //     num.second);

    return 0;
}
