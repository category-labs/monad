// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include "runloop_ethereum.hpp"
#include "runloop_monad.hpp"

#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/likely.h>
#include <category/core/procfs/statm.h>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/chain/genesis_state.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/log_level_map.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/db_cache.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/chain/monad_testnet2.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/statesync/statesync_server.h>
#include <category/statesync/statesync_server_context.hpp>
#include <category/statesync/statesync_server_network.hpp>
#include <category/vm/vm.hpp>

#include <CLI/CLI.hpp>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/handlers/FileHandler.h>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <limits>
#include <optional>
#include <signal.h>
#include <stdexcept>
#include <string>
#include <sys/sysinfo.h>
#include <unistd.h>
#include <vector>

MONAD_NAMESPACE_BEGIN

extern quill::Logger *event_tracer;

MONAD_NAMESPACE_END

sig_atomic_t volatile stop;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void signal_handler(int)
{
    stop = 1;
}

std::terminate_handler cxx_runtime_terminate_handler;

extern "C" void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool print_async_unsafe_info);

void backtrace_terminate_handler()
{
    char buffer[16384];
    monad_stack_backtrace_capture_and_print(
        buffer,
        sizeof(buffer),
        STDERR_FILENO,
        /*indent*/ 3,
        /*print_async_unsafe_info*/ true);

    // Now that we've printed the trace, delegate the actual termination to the
    // handler originally installed by the C++ runtime support library
    cxx_runtime_terminate_handler();
}

MONAD_ANONYMOUS_NAMESPACE_END

using namespace monad;
namespace fs = std::filesystem;

int main(int const argc, char const *argv[])
{
    cxx_runtime_terminate_handler = std::get_terminate();
    std::set_terminate(backtrace_terminate_handler);

    CLI::App cli{"monad"};
    cli.option_defaults()->always_capture_default();

    monad_chain_config chain_config;
    fs::path block_db_path;
    uint64_t nblocks = std::numeric_limits<uint64_t>::max();
    unsigned nthreads = 4;
    unsigned nfibers = 256;
    bool no_compaction = false;
    bool trace_calls = false;
    unsigned sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    unsigned ro_sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 2);
    std::vector<fs::path> dbname_paths;
    fs::path snapshot;
    fs::path dump_snapshot;
    std::string statesync;
    auto log_level = quill::LogLevel::Info;

    std::unordered_map<std::string, monad_chain_config> const CHAIN_CONFIG_MAP =
        {{"ethereum_mainnet", CHAIN_CONFIG_ETHEREUM_MAINNET},
         {"monad_devnet", CHAIN_CONFIG_MONAD_DEVNET},
         {"monad_testnet", CHAIN_CONFIG_MONAD_TESTNET},
         {"monad_mainnet", CHAIN_CONFIG_MONAD_MAINNET},
         {"monad_testnet2", CHAIN_CONFIG_MONAD_TESTNET2}};

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
    cli.add_flag("--trace_calls", trace_calls, "enable call tracing");
    auto *const group =
        cli.add_option_group("load", "methods to initialize the db");
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
    group->require_option(0, 1);
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
        "%(time) [%(thread_id)] %(file_name):%(line_number) LOG_%(log_level)\t"
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

    enable_call_tracing(trace_calls);

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
                    .rewind_to_latest_finalized = true,
                    .rd_buffers = 8192,
                    .wr_buffers = 32,
                    .uring_entries = 128,
                    .sq_thread_cpu = sq_thread_cpu,
                    .dbname_paths = dbname_paths}};
        }
        machine = std::make_unique<InMemoryMachine>();
        return mpt::Db{*machine};
    }();

    auto chain = [chain_config] -> std::unique_ptr<Chain> {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return std::make_unique<EthereumMainnet>();
        case CHAIN_CONFIG_MONAD_DEVNET:
            return std::make_unique<MonadDevnet>();
        case CHAIN_CONFIG_MONAD_TESTNET:
            return std::make_unique<MonadTestnet>();
        case CHAIN_CONFIG_MONAD_MAINNET:
            return std::make_unique<MonadMainnet>();
        case CHAIN_CONFIG_MONAD_TESTNET2:
            return std::make_unique<MonadTestnet2>();
        }
        MONAD_ASSERT(false);
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
            LOG_INFO("loading from genesis");
            GenesisState const genesis_state = chain->get_genesis_state();
            load_genesis_state(genesis_state, triedb);
        }
        return triedb.get_block_number();
    }();

    std::unique_ptr<monad_statesync_server_context> ctx;
    std::jthread sync_thread;
    monad_statesync_server *sync = nullptr;
    if (!statesync.empty()) {
        ctx = std::make_unique<monad_statesync_server_context>(triedb);
        sync = monad_statesync_server_create(
            ctx.get(),
            &net.value(),
            &statesync_server_recv,
            &statesync_server_send_upsert,
            &statesync_server_send_done);
        sync_thread = std::jthread([&](std::stop_token const token) {
            pthread_setname_np(pthread_self(), "statesync thread");
            mpt::AsyncIOContext io_ctx{mpt::ReadOnlyOnDiskDbConfig{
                .sq_thread_cpu = ro_sq_thread_cpu,
                .dbname_paths = dbname_paths}};
            mpt::Db ro{io_ctx};
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
        db.get_latest_finalized_version(),
        db.get_latest_verified_version(),
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

    BlockHashBufferFinalized block_hash_buffer;
    bool initialized_headers_from_triedb = false;

    if (!db_in_memory) {
        mpt::AsyncIOContext io_ctx{mpt::ReadOnlyOnDiskDbConfig{
            .sq_thread_cpu = ro_sq_thread_cpu, .dbname_paths = dbname_paths}};
        mpt::Db rodb{io_ctx};
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
    uint64_t const end_block_num =
        (std::numeric_limits<uint64_t>::max() - block_num + 1) <= nblocks
            ? std::numeric_limits<uint64_t>::max()
            : block_num + nblocks - 1;

    vm::VM vm;
    DbCache db_cache = ctx ? DbCache{*ctx} : DbCache{triedb};
    auto const result = [&] {
        switch (chain_config) {
        case CHAIN_CONFIG_ETHEREUM_MAINNET:
            return runloop_ethereum(
                *chain,
                block_db_path,
                db_cache,
                vm,
                block_hash_buffer,
                priority_pool,
                block_num,
                end_block_num,
                stop);
        case CHAIN_CONFIG_MONAD_DEVNET:
        case CHAIN_CONFIG_MONAD_TESTNET:
        case CHAIN_CONFIG_MONAD_MAINNET:
        case CHAIN_CONFIG_MONAD_TESTNET2:
            return runloop_monad(
                dynamic_cast<MonadChain const &>(*chain),
                block_db_path,
                db,
                db_cache,
                vm,
                block_hash_buffer,
                priority_pool,
                block_num,
                end_block_num,
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
        mpt::AsyncIOContext io_ctx(
            mpt::ReadOnlyOnDiskDbConfig{
                .sq_thread_cpu = ro_sq_thread_cpu,
                .dbname_paths = dbname_paths,
                .concurrent_read_io_limit = 128});
        mpt::Db db{io_ctx};
        TrieDb ro_db{db};
        write_to_file(ro_db.to_json(), dump_snapshot, block_num);
    }
    return result.has_error() ? EXIT_FAILURE : EXIT_SUCCESS;
}
