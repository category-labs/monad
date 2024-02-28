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
#include <sstream>

#include <sys/sysinfo.h>

MONAD_NAMESPACE_BEGIN

using current_fork = fork_traits::shanghai;

static constexpr auto beneficiary =
    0x388C818CA8B9251b393131C08a736A67ccB19297_address;
static constexpr uint256_t base_fee_per_gas = 1'000'000'000u;
std::string global_value;

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
        // std::cout << line << std::endl;
        std::getline(ss, address, ',');
        // std::cout << address << std::endl;
        std::getline(ss, address);
        // std::cout << address << std::endl;

        address = address.substr(2, 42);
        // std::cout << address << std::endl;
        Address formatted_address =
            evmc::from_hex<monad::Address>(address).value();
        addresses.emplace_back(std::move(formatted_address));
    }

    return addresses;
}

Block make_block(byte_string_view &encoded_txns)
{
    Block block;
    BlockHeader block_header;
    block_header.beneficiary = beneficiary;
    block_header.base_fee_per_gas = std::make_optional(base_fee_per_gas);

    auto txns = rlp::decode_transaction_vector(encoded_txns);
    if (txns.has_error()) {
        LOG_INFO("Decode error: {}", txns.assume_error().value());
    }
    MONAD_ASSERT(!txns.has_error());

    block.transactions = std::move(txns.value());

    return block;
}

MONAD_NAMESPACE_END

int main(int argc, char *argv[])
{
    using namespace monad;

    CLI::App cli{"lob"};

    std::filesystem::path block_db_path{};
    uint64_t finish_batch = 1500;

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

    cli.add_option(
        "--finish_batch", finish_batch, "Last batch of txn to execute");
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
    quill::get_root_logger()->set_log_level(log_level);

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
    auto db = db::TrieDb{config};
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
        block_state.commit();
    }

    LOG_INFO("Finished adding balance to relevant accounts");

    // execute setup txns
    {
        auto block_byte_string = get(block_db_path, /*setup*/ true, 0);
        MONAD_ASSERT(block_byte_string);
        Block setup_block = make_block(block_byte_string.value());
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
    }

    LOG_INFO("Finished executing setup transactions");
    auto const start_time = std::chrono::steady_clock::now();

    // execute other txns

    for (uint64_t i = 0; i < std::min(finish_batch, uint64_t{1500}); ++i) {
        auto block_byte_string = get(block_db_path, /*setup*/ false, i);
        MONAD_ASSERT(block_byte_string);
        Block setup_block = make_block(block_byte_string.value());
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

    auto const num = db.count();

    LOG_INFO(
        "Finished running, num files = {}, num transactions = {}k, time "
        "elasped = {}, tps = {}",
        std::min(finish_batch, uint64_t{1500}),
        std::min(finish_batch, uint64_t{1500}),
        time_elapsed,
        finish_batch * 1000 /
            std::max(1UL, static_cast<uint64_t>(time_elapsed.count())));

    LOG_INFO(
        "Number of accounts = {}, number of storage = {}",
        num.first,
        num.second);

    return 0;
}
