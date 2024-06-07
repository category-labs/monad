#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/fmt/receipt_fmt.hpp>
#include <monad/core/log_level_map.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/db/db_cache.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/db.hpp>
#include <monad/state2/block_state.hpp>

#include <CLI/CLI.hpp>
#include <quill/Quill.h>

#include <chrono>
#include <filesystem>
#include <sys/sysinfo.h>

using namespace monad;
namespace fs = std::filesystem;

MONAD_NAMESPACE_BEGIN

quill::Logger *tracer = nullptr;

MONAD_NAMESPACE_END

static sig_atomic_t volatile stop;

static void prefetch_db_into_memory(TrieDb &db) {
    LOG_INFO("Loading current root into memory");
    auto const start_time = std::chrono::steady_clock::now();
    auto const nodes_loaded = db.prefetch_current_root();
    auto const finish_time = std::chrono::steady_clock::now();
    auto const elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        finish_time - start_time);
    LOG_INFO(
        "Finish loading current root into memory, time_elapsed = {}, "
        "nodes_loaded = {}",
        elapsed,
        nodes_loaded);
}

static TrieDb make_db(
        std::optional<mpt::OnDiskDbConfig> const &config,
        fs::path const &snapshot) {
    if (snapshot.empty()) {
        return TrieDb{config};
    }
    if (!(fs::is_directory(snapshot) &&
            fs::exists(snapshot / "accounts") &&
            fs::exists(snapshot / "code"))) {
        throw std::runtime_error(
            "Invalid snapshot folder provided. Please ensure that the "
            "directory you pass contains the block number of the snapshot "
            "in its path and includes files 'accounts' and 'code'.");
    }
    uint64_t init_block_number = std::stoul(snapshot.stem());
    MONAD_ASSERT(fs::exists(snapshot / "code"));
    LOG_INFO("Loading from binary checkpoint in {}", snapshot);
    std::ifstream accounts(snapshot / "accounts");
    std::ifstream code(snapshot / "code");
    return TrieDb{config, accounts, code, init_block_number};
}

static void signal_handler(int)
{
    stop = 1;
}

static bool is_null_or_gt(
        std::optional<uint64_t> const left, uint64_t right) {
    if (!left.has_value())
        return true;
    return left.value() > right;
}

static BlockHashBuffer make_block_hash_buffer(
        uint64_t start_block_number, BlockDb &block_db) {
    BlockHashBuffer block_hash_buffer;
    uint64_t block_number =
        start_block_number < 256 ? 1 : start_block_number - 255;
    for (; block_number < start_block_number; ++block_number) {
        Block block{};
        bool const result = block_db.get(block_number, block);
        MONAD_ASSERT(result);
        block_hash_buffer.set(block_number - 1, block.header.parent_hash);
    }
    return block_hash_buffer;
}

static bool verify_root_hash(
    evmc_revision const rev, BlockHeader const &block_header,
    bytes32_t const receipts_root, bytes32_t const state_root)
{
    if (state_root != block_header.state_root) {
        LOG_ERROR(
            "Block: {}, Computed State Root: {}, Expected State Root: {}",
            block_header.number,
            state_root,
            block_header.state_root);
        return false;
    }
    if (MONAD_LIKELY(rev >= EVMC_BYZANTIUM)) {
        if (receipts_root != block_header.receipts_root) {
            LOG_ERROR(
                "Block: {}, Computed Receipts Root: {}, Expected Receipts "
                "Root: {}",
                block_header.number,
                receipts_root,
                block_header.receipts_root);
            return false;
        }
    }
    return true;
}

static std::tuple<bool, uint64_t, uint64_t>
run_monad(BlockDb &block_db, Db &db, fiber::PriorityPool &priority_pool,
    uint64_t start_block_number, std::optional<uint64_t> const nblocks)
{
    bool result_success = true;
    uint64_t new_blocks_count = 0;
    uint64_t new_transactions_count = 0;

    stop = 0;
    signal(SIGINT, signal_handler);

    // TODO: replace with monad specfiic mainnet
    EthereumMainnet const chain{};

    BlockHashBuffer block_hash_buffer =
        make_block_hash_buffer(start_block_number, block_db);

    while (stop == 0 && is_null_or_gt(nblocks, new_blocks_count)) {
        uint64_t block_number = start_block_number + new_blocks_count;
        if (MONAD_UNLIKELY(!block_number)) {
            LOG_ERROR(
                "block number out of bounds with new blocks count = {}",
                new_blocks_count);
            result_success = false;
            break; // wrapped
        }

        Block block{};
        if (!block_db.get(block_number, block)) {
            if (nblocks != std::nullopt)
                continue;
            result_success = false;
            break;
        }

        block_hash_buffer.set(block_number - 1, block.header.parent_hash);

        auto result = chain.static_validate_header(block.header);
        if (MONAD_UNLIKELY(result.has_error())) {
            LOG_ERROR(
                "block {} header validation failed: {}",
                block.header.number,
                result.assume_error().message().c_str());
            result_success = false;
            break;
        }

        evmc_revision const rev = chain.get_revision(block.header);

        result = static_validate_block(rev, block);
        if (MONAD_UNLIKELY(result.has_error())) {
            LOG_ERROR(
                "block {} validation failed: {}",
                block.header.number,
                result.assume_error().message().c_str());
            result_success = false;
            break;
        }

        auto const before = std::chrono::steady_clock::now();
        BlockState block_state(db);
        auto const receipts = execute_block(
            rev, block, block_state, block_hash_buffer, priority_pool);
        if (receipts.has_error()) {
            LOG_ERROR(
                "block {} tx validation failed: {}",
                block.header.number,
                receipts.assume_error().message().c_str());
            result_success = false;
            break;
        }
        result = validate_header(receipts.assume_value(), block.header);
        if (result.has_error()) {
            LOG_ERROR(
                "when executing block: {}",
                result.assume_error().message().c_str());
            result_success = false;
            break;
        }

        LOG_DEBUG("generated receipts {}", receipts.assume_value());
        block_state.log_debug();
        block_state.commit(receipts.assume_value());

        LOG_DEBUG(
            "finished executing {} txs in block {}, time elasped={}",
            block.transactions.size(),
            block.header.number,
            std::chrono::steady_clock::now() - before);

        if (!verify_root_hash(
                rev,
                block.header,
                db.receipts_root(),
                db.state_root())) {
            result_success = false;
            break;
        }

        ++new_blocks_count;
        new_transactions_count += block.transactions.size();
    }

    return {result_success, new_transactions_count, new_blocks_count};
}

int main(int const argc, char const *argv[])
{
    using namespace monad;

    CLI::App cli{"monad"};
    cli.option_defaults()->always_capture_default();

    fs::path block_db_path{};
    fs::path genesis_file_path{};
    fs::path trace_log = fs::absolute("trace");
    std::vector<fs::path> dbname_paths;
    uint64_t nblocks;
    unsigned nthreads = 4;
    unsigned nfibers = 256;
    bool no_compaction = false;
    unsigned sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    fs::path load_snapshot{};
    fs::path dump_snapshot{};
    auto log_level = quill::LogLevel::Info;

    cli.add_option("--block_db", block_db_path, "block_db directory")->required();
    cli.add_option("--trace_log", trace_log, "path to output trace file");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    auto *has_genesis_file = cli.add_option(
        "--genesis_file", genesis_file_path, "genesis file directory")
        ->check(CLI::ExistingFile);
    auto *has_nblocks = cli.add_option(
            "--nblocks", nblocks,
            "number of blocks to execute (unbounded when unspecified)");
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_flag("--no_compaction", no_compaction, "disable compaction");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "sq_thread_cpu field in io_uring_params, to specify the cpu set "
        "kernel poll thread is bound to in SQPOLL mode");
    cli.add_option(
        "--db",
        dbname_paths,
        "A comma-separated list of previously created database paths. You can "
        "configure the storage pool with one or more files/devices. If no "
        "value is passed, monad will run with an in-memory triedb");
    cli.add_option(
        "--load_snapshot", load_snapshot, "snapshot file path to load db from");
    cli.add_option(
        "--dump_snapshot",
        dump_snapshot,
        "directory to dump state to at the end of run");

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }

    auto file_handler = quill::stdout_handler();
    file_handler->set_pattern(
        "%(ascii_time) [%(thread)] %(filename):%(lineno) LOG_%(level_name)\t"
        "%(message)",
        "%Y-%m-%d %H:%M:%S.%Qns",
        quill::Timezone::LocalTime);
    quill::Config cfg;
    cfg.default_handlers.emplace_back(file_handler);
    quill::configure(cfg);
    quill::start(true);
#ifdef ENABLE_TRACING
    quill::FileHandlerConfig handler_cfg;
    handler_cfg.set_pattern("%(message)", "");
    tracer = quill::create_logger(
        "trace", quill::file_handler(trace_log, handler_cfg));
#endif
    quill::get_root_logger()->set_log_level(log_level);

    LOG_INFO("running with commit '{}'", GIT_COMMIT_HASH);

    BlockDb block_db{block_db_path};

    auto const before = std::chrono::steady_clock::now();
    auto const config = !dbname_paths.empty()
                            ? std::make_optional(mpt::OnDiskDbConfig{
                                  .append = true, // always open existing
                                  .compaction = !no_compaction,
                                  .rd_buffers = 8192,
                                  .wr_buffers = 32,
                                  .uring_entries = 128,
                                  .sq_thread_cpu = sq_thread_cpu,
                                  .dbname_paths = dbname_paths})
                            : std::nullopt;
    auto db = make_db(config, load_snapshot);
    if (load_snapshot.empty()) {
        prefetch_db_into_memory(db);
    }

    if (db.get_block_number() == 0) {
        MONAD_ASSERT(*has_genesis_file);
        read_and_verify_genesis(block_db, db, genesis_file_path);
    }
    LOG_INFO(
        "Finished initializing db at block = {}, time elapsed = {}",
        db.get_block_number(),
        std::chrono::steady_clock::now() - before);

    uint64_t start_block_number = db.get_block_number() + 1;

    LOG_INFO(
        "Running with block_db = {}, start block number = {}, "
        "number blocks = {}",
        block_db_path,
        start_block_number,
        *has_nblocks ? std::to_string(nblocks) : "unbounded");

    fiber::PriorityPool priority_pool{nthreads, nfibers};
    auto const start_time = std::chrono::steady_clock::now();
    DbCache db_cache{db};

    auto nblocks_opt =
        *has_nblocks ? std::make_optional(nblocks) : std::nullopt;
    auto [success, new_transactions_count, new_blocks_count] =
        run_monad(block_db, db_cache, priority_pool,
                start_block_number, nblocks_opt);
    if (!success) {
        return EXIT_FAILURE;
    }

    uint64_t const last_block_number = start_block_number + new_blocks_count - 1;
    auto const finish_time = std::chrono::steady_clock::now();
    auto const elapsed = std::chrono::duration_cast<std::chrono::seconds>(
        finish_time - start_time);
    auto tps = new_transactions_count /
        std::max(1UL, static_cast<uint64_t>(elapsed.count()));
    LOG_INFO(
        "Finish running, finish(stopped) block number = {}, "
        "number of blocks run = {}, time_elapsed = {}, num transactions = {}, "
        "tps = {}",
        last_block_number,
        new_blocks_count,
        elapsed,
        new_transactions_count,
        tps);

    if (stop == 1) {
        // Exit because of received interrupt.
        return 0;
    }

    if (!dump_snapshot.empty()) {
        LOG_INFO("Dump db of block: {}", last_block_number);
        write_to_file(db.to_json(), dump_snapshot, last_block_number);
    }

    return 0;
}
