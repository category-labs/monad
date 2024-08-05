#include <monad/chain/monad_devnet.hpp>
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
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/mpt/db.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>
#include <monad/statesync/statesync_server_network.hpp>

#include <CLI/CLI.hpp>
#include <quill/Quill.h>

#include <chrono>
#include <filesystem>
#include <optional>
#include <sys/sysinfo.h>

using namespace monad;
namespace fs = std::filesystem;

MONAD_NAMESPACE_BEGIN

quill::Logger *event_tracer = nullptr;

MONAD_NAMESPACE_END

sig_atomic_t volatile stop;

void signal_handler(int)
{
    stop = 1;
}

void run_monad(
    Chain const &chain, fs::path const &block_db, Db &db,
    fiber::PriorityPool &priority_pool, size_t block_number)
{
    BlockHashBuffer block_hash_buffer;

    auto const try_get = [&block_db](uint64_t const i, Block &block) {
        auto const path = block_db / std::to_string(i);
        if (!fs::exists(path)) {
            return false;
        }
        MONAD_ASSERT(fs::is_regular_file(path));
        std::ifstream istream(path);
        std::ostringstream buf;
        buf << istream.rdbuf();
        auto view = byte_string_view{
            (unsigned char *)buf.view().data(), buf.view().size()};
        auto block_result = rlp::decode_block(view);
        if (block_result.has_error()) {
            return false;
        }
        MONAD_ASSERT(view.empty());
        block = block_result.assume_value();
        return true;
    };

    Block block;
    for (size_t i = block_number < 256 ? 1 : block_number - 255;
         i < block_number;) {
        if (!try_get(i, block)) {
            continue;
        }
        block_hash_buffer.set(i - 1, block.header.parent_hash);
        ++i;
    }

    signal(SIGINT, signal_handler);
    stop = 0;

    while (stop == 0) {
        if (!try_get(block_number, block)) {
            continue;
        }

        block_hash_buffer.set(block_number - 1, block.header.parent_hash);

        auto result = chain.static_validate_header(block.header);
        if (MONAD_UNLIKELY(result.has_error())) {
            LOG_ERROR(
                "block {} header validation failed: {}",
                block.header.number,
                result.assume_error().message().c_str());
            break;
        }

        auto const rev = chain.get_revision(block.header);

        result = static_validate_block(rev, block);
        if (MONAD_UNLIKELY(result.has_error())) {
            LOG_ERROR(
                "block {} validation failed: {}",
                block.header.number,
                result.assume_error().message().c_str());
            break;
        }

        auto const before = std::chrono::steady_clock::now();
        BlockState block_state(db);
        auto const receipts = execute_block(
            chain, rev, block, block_state, block_hash_buffer, priority_pool);
        if (receipts.has_error()) {
            LOG_ERROR(
                "block {} tx validation failed: {}",
                block.header.number,
                receipts.assume_error().message().c_str());
            break;
        }

        LOG_DEBUG("generated receipts {}", receipts.assume_value());
        block_state.log_debug();
        block_state.commit(receipts.assume_value());

        LOG_INFO(
            "finished executing {} txs in block {}, time elasped={}",
            block.transactions.size(),
            block.header.number,
            std::chrono::steady_clock::now() - before);
        ++block_number;
    }
}

int main(int const argc, char const *argv[])
{
    using namespace monad;

    CLI::App cli{"monad"};
    cli.option_defaults()->always_capture_default();

    fs::path block_db{};
    fs::path genesis_file{};
    fs::path trace_log = std::filesystem::absolute("trace");
    std::vector<std::filesystem::path> dbname_paths;
    unsigned nthreads = 4;
    unsigned nfibers = 32;
    unsigned sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    unsigned sync_sq_thread_cpu = static_cast<unsigned>(get_nprocs() - 1);
    auto log_level = quill::LogLevel::Info;
    std::string statesync_path;

    cli.add_option("--block_db", block_db, "block_db directory")->required();
    cli.add_option("--trace_log", trace_log, "path to output trace file");
    cli.add_option("--genesis_file", genesis_file, "genesis file directory")
        ->required()
        ->check(CLI::ExistingFile);
    cli.add_option("--log_level", log_level, "level of logging")
        ->transform(CLI::CheckedTransformer(log_level_map, CLI::ignore_case));
    cli.add_option("--nthreads", nthreads, "number of threads");
    cli.add_option("--nfibers", nfibers, "number of fibers");
    cli.add_option(
        "--sq_thread_cpu",
        sq_thread_cpu,
        "sq_thread_cpu field in io_uring_params, to specify the cpu set "
        "kernel poll thread is bound to in SQPOLL mode");
    cli.add_option(
        "--sync_sq_thread_cpu",
        sync_sq_thread_cpu,
        "sq_thread_cpu for the state sync read only db");
    cli.add_option(
           "--db",
           dbname_paths,
           "a space delimited list of previously created database paths. "
           "the storage pool may be configured with one or more files/devices. "
           "if no value is passed, the replay will run with an in-memory "
           "triedb")
        ->check(CLI::ExistingPath);
    cli.add_option(
        "--statesync_path", statesync_path, "used for statesync communication");

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
        quill::Timezone::GmtTime);
    quill::Config cfg;
    cfg.default_handlers.emplace_back(file_handler);
    quill::configure(cfg);
    quill::start(true);
#ifdef ENABLE_EVENT_TRACING
    quill::FileHandlerConfig handler_cfg;
    handler_cfg.set_pattern("%(message)", "");
    event_tracer = quill::create_logger(
        "event_trace", quill::file_handler(trace_log, handler_cfg));
#endif
    quill::get_root_logger()->set_log_level(log_level);

    LOG_INFO("running with commit '{}'", GIT_COMMIT_HASH);

    auto const before = std::chrono::steady_clock::now();
    std::optional<monad_statesync_server_network> net;
    if (!statesync_path.empty()) {
        net.emplace(statesync_path.c_str());
    }
    std::unique_ptr<mpt::StateMachine> machine;
    mpt::Db db = [&] {
        if (!dbname_paths.empty()) {
            machine = std::make_unique<OnDiskMachine>();
            return mpt::Db{
                *machine,
                mpt::OnDiskDbConfig{
                    .append = true,
                    .compaction = true,
                    .rd_buffers = 8192,
                    .wr_buffers = 32,
                    .uring_entries = 128,
                    .sq_thread_cpu = sq_thread_cpu,
                    .dbname_paths = dbname_paths}};
        }
        machine = std::make_unique<InMemoryMachine>();
        return mpt::Db{*machine};
    }();
    TrieDb triedb{db};
    std::optional<monad_statesync_server_context> ctx;
    std::jthread sync_thread;
    monad_statesync_server *sync = nullptr;
    if (!statesync_path.empty()) {
        MONAD_ASSERT(db.root().is_valid());
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
                .sq_thread_cpu = sync_sq_thread_cpu,
                .dbname_paths = dbname_paths}};
            ctx->ro = &ro;
            while (!token.stop_requested()) {
                monad_statesync_server_run_once(sync);
            }
            ctx->ro = nullptr;
        });
    }

    if (!db.root().is_valid()) {
        read_genesis(genesis_file, triedb);
    }

    LOG_INFO(
        "finished initializing db at block {}, time elapsed = {}",
        triedb.get_block_number(),
        std::chrono::steady_clock::now() - before);

    fiber::PriorityPool priority_pool{nthreads, nfibers};
    auto const start_time = std::chrono::steady_clock::now();
    auto db_cache = [&] {
        if (sync) {
            return DbCache{*ctx};
        }
        return DbCache{triedb};
    }();

    MonadDevnet const chain{};
    run_monad(
        chain,
        block_db,
        db_cache,
        priority_pool,
        triedb.get_block_number() + 1);
    LOG_INFO(
        "finished running, time_elapsed = {}",
        std::chrono::steady_clock::now() - start_time);

    if (sync) {
        sync_thread.request_stop();
        sync_thread.join();
        monad_statesync_server_destroy(sync);
    }

    return 0;
}
