#include <monad/core/assert.h>
#include <monad/core/async_signal_handling.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/hex_literal.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/test/test_fixtures_base.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <CLI/CLI.hpp>

#include <quill/Quill.h>

#include <atomic>
#include <chrono>
#include <filesystem>
#include <limits>
#include <list>
#include <thread>
#include <utility>

#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>

using namespace monad::mpt;
using namespace monad::test;

static_assert(std::atomic<bool>::is_always_lock_free); // async signal safe

static monad::hash256 to_key(uint64_t const key)
{
    auto const as_bytes = serialize_as_big_endian<sizeof(key)>(key);
    return monad::keccak256(as_bytes);
}

static uint64_t
select_rand_version(Db const &db, monad::small_prng &rnd, double bias)
{
    auto const version_range_start =
        static_cast<double>(db.get_earliest_block_id());
    auto const version_range_end =
        static_cast<double>(db.get_latest_block_id());
    double r = rnd();
    r = r / monad::small_prng::max();
    if (r > 0.25) {
        r = std::pow(r, bias);
    }
    return static_cast<uint64_t>(
        version_range_start + r * (version_range_end - version_range_start));
}

int main(int argc, char *const argv[])
{
    auto async_signal_handling_installation = monad::async_signal_handling();

    unsigned num_sync_reader_threads = 4;
    unsigned num_async_reader_threads = 2;
    size_t num_async_reads_inflight = 100;
    unsigned num_traverse_threads = 2;
    double prng_bias = 1.66;
    size_t num_nodes_per_version = 1;
    bool enable_compaction = true;
    uint32_t timeout_seconds = std::numeric_limits<uint32_t>::max();
    std::vector<std::filesystem::path> dbname_paths;
    CLI::App cli(
        "Tool for stress testing concurrent RO DB instances",
        "read_only_db_stress_test");

    try {
        cli.add_option(
            "--num-sync-reader-threads",
            num_sync_reader_threads,
            "Number of threads doing random blocking reads");
        cli.add_option(
            "--num-async-reader-threads",
            num_async_reader_threads,
            "Number of threads doing random async reads");
        cli.add_option(
            "--num-async-reads-inflight",
            num_async_reads_inflight,
            "Number of async reads to issue before calling poll");
        cli.add_option(
            "--num-traverse-threads",
            num_traverse_threads,
            "Number of threads traversing random version tries");
        cli.add_option(
            "--prng-bias",
            prng_bias,
            "After drawing R, raises r**bias. Can be used to choose versions "
            "earlier or later in the history");
        cli.add_option(
            "--compaction",
            enable_compaction,
            "Enable compaction when writing new DB versions");
        cli.add_option(
            "--num-nodes-per-version",
            num_nodes_per_version,
            "Number of nodes to upsert per version");
        cli.add_option(
            "--timeout",
            timeout_seconds,
            "Teardown the stress test after N seconds");
        cli.add_option(
               "--db",
               dbname_paths,
               "A comma-separated list of previously created database paths")
            ->required();
        cli.parse(argc, argv);

        quill::start(true);

        static std::atomic<bool> g_done{false};
        auto sigint_handler = monad::async_signal_handling::add_handler(
            SIGINT,
            0,
            [](const struct signalfd_siginfo &,
               monad::async_signal_handling::handler *) -> bool {
                g_done = true;
                return true;
            });
        auto mark_sigint_handler_handled = monad::make_scope_exit(
            [&]() noexcept { sigint_handler->mark_as_handled(); });

        auto const prefix = 0x00_hex;

        auto upsert_new_version = [&](Db &db, uint64_t const version) {
            UpdateList ul;

            std::list<monad::hash256> hash_alloc;
            std::list<Update> update_alloc;
            auto const version_bytes =
                serialize_as_big_endian<sizeof(uint64_t)>(version);
            for (size_t k = 0; k < num_nodes_per_version; ++k) {
                ul.push_front(update_alloc.emplace_back(make_update(
                    hash_alloc.emplace_back(
                        to_key(version * num_nodes_per_version + k)),
                    version_bytes)));
            }

            auto u_prefix = Update{
                .key = prefix,
                .value = monad::byte_string_view{},
                .incarnation = false,
                .next = std::move(ul)};
            UpdateList ul_prefix;
            ul_prefix.push_front(u_prefix);

            db.upsert(std::move(ul_prefix), version);
        };

        auto random_sync_read = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            AsyncIOContext io_ctx{ro_config};
            Db ro_db{io_ctx};

            while (ro_db.get_latest_block_id() == INVALID_BLOCK_ID &&
                   !g_done.load(std::memory_order_acquire)) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_block_id() != INVALID_BLOCK_ID);
            MONAD_ASSERT(ro_db.get_earliest_block_id() != INVALID_BLOCK_ID);

            unsigned nsuccess = 0;
            unsigned nfailed = 0;

            auto rnd = monad::thread_local_prng();
            while (!g_done.load(std::memory_order_acquire)) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);
                auto const version_bytes =
                    serialize_as_big_endian<sizeof(uint64_t)>(version);

                for (size_t k = 0; k < num_nodes_per_version; ++k) {
                    auto const res = ro_db.get(
                        concat(
                            NibblesView{prefix},
                            NibblesView{
                                to_key(version * num_nodes_per_version + k)}),
                        version);
                    if (res.has_value()) {
                        MONAD_ASSERT(res.value() == version_bytes);
                        ++nsuccess;
                    }
                    else {
                        auto const min_version = ro_db.get_earliest_block_id();
                        MONAD_ASSERT(version < min_version);
                        ++nfailed;
                        break;
                    }
                }
            }
            std::ostringstream oss;
            oss << "Sync Reader thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed reads" << std::endl;
            std::cout << oss.str();
        };

        auto random_async_read = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            AsyncIOContext io_ctx{ro_config};
            Db ro_db{io_ctx};
            auto async_ctx = async_context_create(ro_db);

            unsigned nsuccess = 0;
            unsigned nfailed = 0;

            while (ro_db.get_latest_block_id() == INVALID_BLOCK_ID &&
                   !g_done.load(std::memory_order_acquire)) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_block_id() != INVALID_BLOCK_ID);
            MONAD_ASSERT(ro_db.get_earliest_block_id() != INVALID_BLOCK_ID);

            struct receiver_t
            {
                size_t *completions;
                Db *db{nullptr};
                unsigned *nsuccess{nullptr};
                unsigned *nfailed{nullptr};
                uint64_t version;
                monad::byte_string version_bytes;

                void set_value(
                    monad::async::erased_connected_operation *state,
                    monad::async::result<monad::byte_string> res)
                {
                    if (res) {
                        MONAD_ASSERT(res.value() == version_bytes);
                        ++(*nsuccess);
                    }
                    else {
                        auto const min_version = db->get_earliest_block_id();
                        MONAD_ASSERT(version < min_version);
                        ++(*nfailed);
                    }
                    ++(*completions);
                    delete state;
                }
            };

            size_t enqueued{};
            size_t completions{};

            auto rnd = monad::thread_local_prng();
            while (!g_done.load(std::memory_order_acquire)) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);
                auto const version_bytes =
                    serialize_as_big_endian<sizeof(uint64_t)>(version);

                for (size_t k = 0; k < num_nodes_per_version; ++k) {
                    auto *state = new auto(monad::async::connect(
                        monad::mpt::make_get_sender(
                            async_ctx.get(),
                            concat(
                                NibblesView{prefix},
                                NibblesView{to_key(
                                    version * num_nodes_per_version + k)}),
                            version),
                        receiver_t{
                            &completions,
                            &ro_db,
                            &nsuccess,
                            &nfailed,
                            version,
                            version_bytes}));
                    state->initiate();
                    ++enqueued;
                }
                if (enqueued > num_async_reads_inflight) {
                    constexpr size_t MAX_TRIEDB_ASYNC_POLLS{300'000};
                    size_t poll_count{0};
                    while (completions < enqueued &&
                           poll_count < MAX_TRIEDB_ASYNC_POLLS) {
                        ro_db.poll(true, std::numeric_limits<size_t>::max());
                        ++poll_count;
                    }
                }
            }
            std::ostringstream oss;
            oss << "Async reader thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed reads" << std::endl;
            std::cout << oss.str();
        };

        auto random_traverse = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            AsyncIOContext io_ctx{ro_config};
            Db ro_db{io_ctx};

            unsigned nsuccess = 0;
            unsigned nfailed = 0;

            while (ro_db.get_latest_block_id() == INVALID_BLOCK_ID &&
                   !g_done.load(std::memory_order_acquire)) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_block_id() != INVALID_BLOCK_ID);
            MONAD_ASSERT(ro_db.get_earliest_block_id() != INVALID_BLOCK_ID);

            struct VersionValidatorMachine : public TraverseMachine
            {
                Nibbles path{};
                size_t num_nodes;
                std::atomic<bool> &done;

                explicit VersionValidatorMachine(
                    size_t num_nodes_, std::atomic<bool> &done_)
                    : num_nodes(num_nodes_)
                    , done(done_)
                {
                }

                virtual bool
                down(unsigned char branch, Node const &node) override
                {
                    if (branch == INVALID_BRANCH) {
                        return true;
                    }
                    path = concat(
                        NibblesView{path}, branch, node.path_nibble_view());

                    if (node.has_value()) {
                        MONAD_ASSERT(path.nibble_size() == KECCAK256_SIZE * 2);
                        uint64_t const version =
                            deserialize_from_big_endian<uint64_t>(node.value());
                        bool found = false;
                        for (size_t k = 0; k < num_nodes; ++k) {
                            if (path ==
                                NibblesView{to_key(version * num_nodes + k)}) {
                                found = true;
                                break;
                            }
                        }
                        MONAD_ASSERT(found);
                    }
                    return !g_done.load(std::memory_order_acquire);
                }

                virtual void up(unsigned char branch, Node const &node) override
                {
                    auto const path_view = NibblesView{path};
                    auto const rem_size = [&] {
                        if (branch == INVALID_BRANCH) {
                            MONAD_ASSERT(path_view.nibble_size() == 0);
                            return 0;
                        }
                        int const rem_size =
                            path_view.nibble_size() - 1 -
                            node.path_nibble_view().nibble_size();
                        MONAD_ASSERT(rem_size >= 0);
                        MONAD_ASSERT(
                            path_view.substr(static_cast<unsigned>(rem_size)) ==
                            concat(branch, node.path_nibble_view()));
                        return rem_size;
                    }();
                    path = path_view.substr(0, static_cast<unsigned>(rem_size));
                }

                virtual std::unique_ptr<TraverseMachine> clone() const override
                {
                    return std::make_unique<VersionValidatorMachine>(*this);
                }
            };

            auto rnd = monad::thread_local_prng();
            while (!g_done.load(std::memory_order_acquire)) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);
                if (auto cursor = ro_db.find(prefix, version);
                    cursor.has_value()) {
                    VersionValidatorMachine machine(
                        num_nodes_per_version, g_done);
                    machine.num_nodes = num_nodes_per_version;
                    if (!ro_db.traverse(cursor.value(), machine, version)) {
                        auto const min_version = ro_db.get_earliest_block_id();
                        MONAD_ASSERT(version < min_version);
                        ++nfailed;
                    }
                    else {
                        ++nsuccess;
                    }
                }
                else {
                    auto const min_version = ro_db.get_earliest_block_id();
                    MONAD_ASSERT(version < min_version);
                    ++nfailed;
                }
            }
            std::ostringstream oss;
            oss << "Traverse thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed traversals" << std::endl;
            std::cout << oss.str();
        };

        auto open_close_read_only = [&]() {
            unsigned nsuccess = 0;
            unsigned nfailed = 0;
            while (!g_done.load(std::memory_order_acquire)) {
                ReadOnlyOnDiskDbConfig const ro_config{
                    .dbname_paths = dbname_paths};
                AsyncIOContext io_ctx{ro_config};
                Db ro_db{io_ctx};
                auto const version = ro_db.get_earliest_block_id() + 1;
                auto const value =
                    serialize_as_big_endian<sizeof(uint64_t)>(version);
                auto const res = ro_db.get(
                    concat(
                        NibblesView{prefix},
                        NibblesView{to_key(version * num_nodes_per_version)}),
                    version);
                if (res.has_value()) {
                    ++nsuccess;
                    MONAD_ASSERT(res.value() == value);
                }
                else {
                    ++nfailed;
                }
            }
            std::ostringstream oss;
            oss << "Open close handle thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << nsuccess << " successful and " << nfailed
                << " failed queries of earliest version root" << std::endl;
            std::cout << oss.str();
        };

        // construct RWDb
        uint64_t version = 0;
        StateMachineAlwaysMerkle machine{};
        OnDiskDbConfig const config{
            .compaction = enable_compaction, .dbname_paths = {dbname_paths}};
        Db db{machine, config};

        std::cout << "Running read only DB stress test..." << std::endl;

        std::vector<std::thread> readers;
        for (unsigned i = 0; i < num_sync_reader_threads; ++i) {
            readers.emplace_back(random_sync_read);
        }

        for (unsigned i = 0; i < num_async_reader_threads; ++i) {
            readers.emplace_back(random_async_read);
        }

        for (unsigned i = 0; i < num_traverse_threads; ++i) {
            readers.emplace_back(random_traverse);
        }
        readers.emplace_back(open_close_read_only);

        monad::async_signal_handling::invoke_after(
            [&] { g_done = true; }, timeout_seconds * 1000000000ULL);
        while (!g_done.load(std::memory_order_acquire)) {
            upsert_new_version(db, version);
            ++version;
        }
        for (auto &t : readers) {
            t.join();
        }

        std::cout << "Writer finished. Max version in RWDb is "
                  << db.get_latest_block_id() << ", min version in RWDb is "
                  << db.get_earliest_block_id() << "\n\n";
    }
    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
    }
    catch (const CLI::RequiredError &e) {
        std::cerr << "FATAL: " << e.what() << "\n\n";
        std::cerr << cli.help() << std::flush;
        return 1;
    }

    return 0;
}
