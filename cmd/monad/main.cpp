#include "runloop_ethereum.hpp"
#include "runloop_monad.hpp"
#include "util.hpp"

#include <monad/chain/chain_config.h>
#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/fmt/bytes_fmt.hpp>
#include <monad/core/likely.h>
#include <monad/core/log_level_map.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/procfs/statm.h>
#include <monad/state2/block_state.hpp>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>
#include <monad/statesync/statesync_server_network.hpp>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/handlers/FileHandler.h>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <optional>
#include <stdexcept>
#include <string>
#include <vector>

#include <signal.h>
#include <sys/sysinfo.h>

MONAD_NAMESPACE_BEGIN

quill::Logger *event_tracer = nullptr;

MONAD_NAMESPACE_END

sig_atomic_t volatile stop;

void signal_handler(int)
{
    stop = 1;
}

using namespace monad;
namespace fs = std::filesystem;

int main(int const argc, char const *argv[])
{

    CLI::App cli{"monad"};
    cli.option_defaults()->always_capture_default();

    monad_chain_config chain_config;
    fs::path block_db_path;
    uint64_t nblocks = std::numeric_limits<uint64_t>::max();
    unsigned nthreads = 4;
    unsigned nfibers = 256;
    bool no_compaction = false;
    unsigned sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    unsigned ro_sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 2);
    std::vector<fs::path> dbname_paths;
    fs::path genesis;
    fs::path snapshot;
    fs::path dump_snapshot;
    std::string statesync;
    auto log_level = quill::LogLevel::Info;

    std::unordered_map<std::string, monad_chain_config> const CHAIN_CONFIG_MAP =
        {{"ethereum_mainnet", CHAIN_CONFIG_ETHEREUM_MAINNET},
         {"monad_devnet", CHAIN_CONFIG_MONAD_DEVNET},
         {"monad_testnet", CHAIN_CONFIG_MONAD_TESTNET}};

    cli.add_option("--chain", chain_config, "select which chain config to run")
        ->transform(CLI::CheckedTransformer(CHAIN_CONFIG_MAP, CLI::ignore_case))
        ->required();
    cli.add_option("--block_db", block_db_path, "block_db directory")
        ->required();
    cli.add_option("--nblocks", nblocks, "number of blocks to execute");
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_flag("--no-compaction", no_compaction, "disable compaction");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "sq_thread_cpu field in io_uring_params, to specify the cpu set "
        "kernel poll thread is bound to in SQPOLL mode");
    cli.add_option(
        "--ro_sq_thread_cpu",
        ro_sq_thread_cpu,
        "sq_thread_cpu for the read only db");
    cli.add_option(
        "--db",
        dbname_paths,
        "A comma-separated list of previously created database paths. You can "
        "configure the storage pool with one or more files/devices. If no "
        "value is passed, the replay will run with an in-memory triedb");
    cli.add_option(
        "--dump_snapshot",
        dump_snapshot,
        "directory to dump state to at the end of run");
    auto *const group =
        cli.add_option_group("load", "methods to initialize the db");
    group->add_option("--genesis", genesis, "genesis file")
        ->check(CLI::ExistingFile);
    group
        ->add_option(
            "--snapshot", snapshot, "snapshot file path to load db from")
        ->check([](std::string const &s) -> std::string {
            fs::path const path{s};
            if (!fs::is_regular_file(path / "accounts")) {
                return "missing accounts";
            }
            if (!fs::is_regular_file(path / "code")) {
                return "missing code";
            }
            return "";
        });
    group->add_option(
        "--statesync", statesync, "socket for statesync communication");
    group->require_option(1);
#ifdef ENABLE_EVENT_TRACING
    fs::path trace_log = fs::absolute("trace");
    cli.add_option("--trace_log", trace_log, "path to output trace file");
#endif

    try {
        cli.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        return cli.exit(e);
    }
    catch (CLI::RequiredError const &e) {
        return cli.exit(e);
    }

    auto stdout_handler = quill::stdout_handler();
    stdout_handler->set_pattern(
        "%(ascii_time) [%(thread)] %(filename):%(lineno) LOG_%(level_name)\t"
        "%(message)",
        "%Y-%m-%d %H:%M:%S.%Qns",
        quill::Timezone::GmtTime);
    quill::Config cfg;
    cfg.default_handlers.emplace_back(stdout_handler);
    quill::configure(cfg);
    quill::start(true);
    quill::get_root_logger()->set_log_level(log_level);
    LOG_INFO("running with commit '{}'", GIT_COMMIT_HASH);

#ifdef ENABLE_EVENT_TRACING
    quill::FileHandlerConfig handler_cfg;
    handler_cfg.set_pattern("%(message)", "");
    event_tracer = quill::create_logger(
        "event_trace", quill::file_handler(trace_log, handler_cfg));
#endif

    auto const db_in_memory = dbname_paths.empty();
    [[maybe_unused]] auto const load_start_time =
        std::chrono::steady_clock::now();

    std::optional<monad_statesync_server_network> net;
    if (!statesync.empty()) {
        net.emplace(statesync.c_str());
    }
    std::unique_ptr<mpt::StateMachine> machine;
    mpt::Db db = [&] {
        if (!db_in_memory) {
            machine = std::make_unique<OnDiskMachine>();
            return mpt::Db{
                *machine,
                mpt::OnDiskDbConfig{
                    .append = true,
                    .compaction = !no_compaction,
                    .rd_buffers = 8192,
                    .wr_buffers = 32,
                    .uring_entries = 128,
                    .sq_thread_cpu = sq_thread_cpu,
                    .dbname_paths = dbname_paths}};
        }
        machine = std::make_unique<InMemoryMachine>();
        return mpt::Db{*machine};
    }();

    TrieDb triedb{db}; // init block number to latest finalized block
    // Note: in memory db block number is always zero
    uint64_t const init_block_num = [&] {
        if (!snapshot.empty()) {
            if (db.root().is_valid()) {
                throw std::runtime_error(
                    "can not load checkpoint into non-empty database");
            }
            LOG_INFO("Loading from binary checkpoint in {}", snapshot);
            std::ifstream accounts(snapshot / "accounts");
            std::ifstream code(snapshot / "code");
            auto const n = std::stoul(snapshot.stem());
            load_from_binary(db, accounts, code, n);

            // load the eth header for snapshot
            BlockDb block_db{block_db_path};
            Block block;
            MONAD_ASSERT_PRINTF(
                block_db.get(n, block), "FATAL: Could not load block %lu", n);
            load_header(db, block.header);
            return n;
        }
        else if (!db.root().is_valid()) {
            MONAD_ASSERT(statesync.empty());
            LOG_INFO("loading from genesis {}", genesis);
            TrieDb tdb{db};
            read_genesis(genesis, tdb);
        }
        return triedb.get_block_number();
    }();

    std::optional<monad_statesync_server_context> ctx;
    std::jthread sync_thread;
    monad_statesync_server *sync = nullptr;
    if (!statesync.empty()) {
        ctx.emplace(triedb);
        sync = monad_statesync_server_create(
            &ctx.value(),
            &net.value(),
            &statesync_server_recv,
            &statesync_server_send_upsert,
            &statesync_server_send_done);
        sync_thread = std::jthread([&](std::stop_token const token) {
            pthread_setname_np(pthread_self(), "statesync thread");
            mpt::Db ro{mpt::ReadOnlyOnDiskDbConfig{
                .sq_thread_cpu = ro_sq_thread_cpu,
                .dbname_paths = dbname_paths}};
            ctx->ro = &ro;
            while (!token.stop_requested()) {
                monad_statesync_server_run_once(sync);
            }
            ctx->ro = nullptr;
        });
    }

    LOG_INFO(
        "Finished initializing db at block = {}, last finalized block = {}, "
        "last verified block = {}, state root = {}, time elapsed "
        "= {}",
        init_block_num,
        db.get_latest_finalized_block_id(),
        db.get_latest_verified_block_id(),
        triedb.state_root(),
        std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - load_start_time));

    uint64_t const start_block_num = init_block_num + 1;

    LOG_INFO(
        "Running with block_db = {}, start block number = {}, "
        "number blocks = {}",
        block_db_path,
        start_block_num,
        nblocks);

    fiber::PriorityPool priority_pool{nthreads, nfibers};

    auto const start_time = std::chrono::steady_clock::now();

    auto chain = [chain_config] -> std::unique_ptr<Chain> {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return std::make_unique<EthereumMainnet>();
        case CHAIN_CONFIG_MONAD_DEVNET:
            return std::make_unique<MonadDevnet>();
        case CHAIN_CONFIG_MONAD_TESTNET:
            return std::make_unique<MonadTestnet>();
        }
        MONAD_ASSERT(false);
    }();

    BlockHashBufferFinalized block_hash_buffer;
    bool initialized_headers_from_triedb = false;

    if (!db_in_memory) {
        mpt::Db rodb{mpt::ReadOnlyOnDiskDbConfig{
            .sq_thread_cpu = ro_sq_thread_cpu, .dbname_paths = dbname_paths}};
        initialized_headers_from_triedb = init_block_hash_buffer_from_triedb(
            rodb, start_block_num, block_hash_buffer);
    }
    if (!initialized_headers_from_triedb) {
        BlockDb block_db{block_db_path};
        MONAD_ASSERT(chain_config == CHAIN_CONFIG_ETHEREUM_MAINNET);
        MONAD_ASSERT(init_block_hash_buffer_from_blockdb(
            block_db, start_block_num, block_hash_buffer));
    }

    signal(SIGINT, signal_handler);
    stop = 0;

    uint64_t block_num = start_block_num;

    auto const result = [&] {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return runloop_ethereum(
                *chain,
                block_db_path,
                ctx ? static_cast<Db &>(*ctx) : static_cast<Db &>(triedb),
                block_hash_buffer,
                priority_pool,
                block_num,
                nblocks,
                stop);
        case CHAIN_CONFIG_MONAD_DEVNET:
        case CHAIN_CONFIG_MONAD_TESTNET:
            return runloop_monad(
                *chain,
                block_db_path,
                ctx ? static_cast<Db &>(*ctx) : static_cast<Db &>(triedb),
                block_hash_buffer,
                priority_pool,
                block_num,
                nblocks,
                stop);
        }
        MONAD_ABORT_PRINTF("Unsupported chain");
    }();

    if (MONAD_UNLIKELY(result.has_error())) {
        LOG_ERROR(
            "block {} failed with: {}",
            block_num,
            result.assume_error().message().c_str());
    }
    else {
        [[maybe_unused]] auto const elapsed =
            std::chrono::duration_cast<std::chrono::seconds>(
                std::chrono::steady_clock::now() - start_time);
        LOG_INFO(
            "Finish running, finish(stopped) block number = {}, "
            "number of blocks run = {}, time_elapsed = {}, num transactions = "
            "{}, "
            "tps = {}, gps = {} M",
            block_num,
            nblocks,
            elapsed,
            result.assume_value().first,
            result.assume_value().first /
                std::max(1UL, static_cast<uint64_t>(elapsed.count())),
            result.assume_value().second /
                (1'000'000 *
                 std::max(1UL, static_cast<uint64_t>(elapsed.count()))));
    }

    if (sync != nullptr) {
        sync_thread.request_stop();
        sync_thread.join();
        monad_statesync_server_destroy(sync);
    }

    if (!dump_snapshot.empty()) {
        LOG_INFO("Dump db of block: {}", block_num);
        mpt::Db db{mpt::ReadOnlyOnDiskDbConfig{
            .sq_thread_cpu = ro_sq_thread_cpu,
            .dbname_paths = dbname_paths,
            .concurrent_read_io_limit = 128}};
        TrieDb ro_db{db};
        write_to_file(ro_db.to_json(), dump_snapshot, block_num);
    }
    return result.has_error() ? EXIT_FAILURE : EXIT_SUCCESS;
}
