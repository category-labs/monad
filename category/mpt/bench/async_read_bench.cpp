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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/core/small_prng.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/test/test_fixtures_base.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

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

sig_atomic_t volatile g_done = 0;

static_assert(std::atomic<bool>::is_always_lock_free); // async signal safe

static monad::byte_string to_key(uint64_t const key)
{
    auto const as_bytes = serialize_as_big_endian<sizeof(key)>(key);
    auto const hash = monad::keccak256(as_bytes);
    return monad::byte_string{hash.bytes, sizeof(hash.bytes)};
}

static uint64_t
select_rand_version(Db const &db, monad::small_prng &rnd, double bias)
{
    auto const version_range_start =
        static_cast<double>(db.get_earliest_version());
    auto const version_range_end = static_cast<double>(db.get_latest_version());
    double r = rnd();
    r = r / monad::small_prng::max();
    if (r > 0.25) {
        r = std::pow(r, bias);
    }
    return static_cast<uint64_t>(
        version_range_start + r * (version_range_end - version_range_start));
}

static void on_signal(int)
{
    g_done = 1;
}

struct OpStats
{
    uint64_t num{0};
    std::chrono::steady_clock::duration time{};
};

struct Stats
{
    std::mutex mutex;
    OpStats lookup;
    OpStats traverse;
};

int main(int argc, char *const argv[])
{
    unsigned num_async_reader_threads = 1;
    size_t num_async_reads_inflight = 100;
    unsigned num_traverse_threads = 0;
    double prng_bias = 1.66;
    size_t num_nodes_per_version = 1;
    uint32_t runtime_seconds = std::numeric_limits<uint32_t>::max();
    unsigned update_delay_ms = 500;
    uint64_t cache_size = 1 * 1024 * 1024;

    Stats total_stats;

    std::vector<std::filesystem::path> dbname_paths;
    CLI::App cli(
        "Benchmark for read-only db async reads and traversals",
        "async_read_bench");

    try {
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
            "After drawing R, raises r**bias. Can be used to choose "
            "versions "
            "earlier or later in the history");
        cli.add_option(
            "--num-nodes-per-version",
            num_nodes_per_version,
            "Number of nodes to upsert per version");
        cli.add_option(
            "--runtime", runtime_seconds, "Limit runtime in seconds");
        cli.add_option(
            "--update-delay",
            update_delay_ms,
            "Delay between upserts in the RWDb in milliseconds");
        cli.add_option(
            "--cache-size",
            cache_size,
            "Size of the node cache (in number of nodes)");
        cli.add_option(
               "--db",
               dbname_paths,
               "A comma-separated list of previously created database paths")
            ->required();

        cli.parse(argc, argv);

        std::cout << "Starting benchmark with the following parameters:"
                  << std::endl;
        std::cout << "  num_async_reader_threads: " << num_async_reader_threads
                  << std::endl;
        std::cout << "  num_async_reads_inflight: " << num_async_reads_inflight
                  << std::endl;
        std::cout << "  num_traverse_threads: " << num_traverse_threads
                  << std::endl;
        std::cout << "  prng_bias: " << prng_bias << std::endl;
        std::cout << "  num_nodes_per_version: " << num_nodes_per_version
                  << std::endl;
        std::cout << "  runtime : " << runtime_seconds << " seconds"
                  << std::endl;
        std::cout << "  update_delay: " << update_delay_ms << " ms"
                  << std::endl;

        quill::start(true);

        struct sigaction sig;
        sig.sa_handler = &on_signal;
        sig.sa_flags = 0;
        sigaction(SIGINT, &sig, nullptr);
        sigaction(SIGALRM, &sig, nullptr);

        std::vector<Nibbles> keys;

        struct CollectKeys : TraverseMachine
        {
            Nibbles path_;

            CollectKeys(std::vector<Nibbles> &keys)
                : keys(keys)
            {
            }

            std::vector<Nibbles> &keys;

            virtual bool down(unsigned char branch, Node const &node) override
            {
                if (branch != INVALID_BRANCH) {
                    if (path_.empty() && branch != 0x1) {
                        return false;
                    }
                    path_ = concat(path_, branch, node.path_nibble_view());
                }

                if (branch != INVALID_BRANCH && node.has_value()) {
                    keys.emplace_back(path_);
                }
                return true;
            }

            virtual void
            up(unsigned char /*branch*/, Node const & /*node*/) override
            {
            }

            virtual std::unique_ptr<TraverseMachine> clone() const override
            {
                return std::make_unique<CollectKeys>(*this);
            }
        };

        std::cout
            << "Collecting keys from the latest version of the database..."
            << std::endl;

        // construct RWDb
        StateMachineAlwaysMerkle machine{};
        auto const config = OnDiskDbConfig{
            .append = true, .compaction = true, .dbname_paths = {dbname_paths}};
        Db rw_db{machine, config};
        auto rw_root = rw_db.load_root_for_version(rw_db.get_latest_version());

        CollectKeys collect_keys(keys);
        ReadOnlyOnDiskDbConfig const ro_config{.dbname_paths = {dbname_paths}};
        AsyncIOContext io_ctx{ro_config};
        Db ro_db{io_ctx};

        auto version = ro_db.get_latest_version();
        auto root = ro_db.load_root_for_version(version);

        MONAD_ASSERT(root != nullptr);

        ro_db.traverse(NodeCursor{root}, collect_keys, version);

        std::sort(keys.begin(), keys.end());

        if (keys.empty()) {
            std::cerr << "No keys found in the latest version of the "
                         "database. Exiting."
                      << std::endl;
            return 1;
        }

        std::cout << "Collected " << keys.size() << " keys from version "
                  << version << std::endl;

        monad::byte_string const long_value(1ul << 19, 5);
        std::vector<monad::byte_string> values_overwrite_keys_mode;
        for (uint64_t i = 0; i < num_nodes_per_version; ++i) {
            values_overwrite_keys_mode.emplace_back(
                long_value + serialize_as_big_endian<8>(i));
        }

        auto const prefix = 0x10_bytes;

        auto upsert_new_version = [&](uint64_t const version) {
            UpdateList ul;
            std::list<monad::byte_string> bytes_alloc;
            std::list<Update> update_alloc;
            auto const version_bytes =
                serialize_as_big_endian<sizeof(uint64_t)>(version);
            for (size_t k = 0; k < num_nodes_per_version; ++k) {
                ul.push_front(update_alloc.emplace_back(make_update(
                    bytes_alloc.emplace_back(
                        to_key(version * num_nodes_per_version + k)),
                    version_bytes,
                    version)));
            }

            auto u_prefix = Update{
                .key = prefix,
                .value = monad::byte_string_view{},
                .incarnation = false,
                .next = std::move(ul),
                .version = (int64_t)version};
            UpdateList ul_prefix;
            ul_prefix.push_front(u_prefix);

            rw_root =
                rw_db.upsert(std::move(rw_root), std::move(ul_prefix), version);
        };

        auto random_async_read = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            AsyncIOContext io_ctx{ro_config};
            Db ro_db{io_ctx};
            auto async_ctx = async_context_create(ro_db, cache_size);

            struct ThreadStats
            {
                uint64_t nsuccess = 0;
                uint64_t nfailed = 0;
                std::chrono::steady_clock::duration total_time{0};
            } thread_stats;

            while (ro_db.get_latest_version() == INVALID_BLOCK_NUM && !g_done) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_version() != INVALID_BLOCK_NUM);
            MONAD_ASSERT(ro_db.get_earliest_version() != INVALID_BLOCK_NUM);

            struct receiver_t
            {
                size_t *completions;
                Db *db{nullptr};
                ThreadStats &stats;
                uint64_t version;
                monad::byte_string version_bytes;
                std::chrono::steady_clock::time_point start_time;

                void set_value(
                    monad::async::erased_connected_operation *state,
                    monad::async::result<monad::byte_string> res)
                {
                    if (res) {
                        ++(stats.nsuccess);
                    }
                    else {
                        ++(stats.nfailed);
                    }
                    ++(*completions);
                    auto const end_time = std::chrono::steady_clock::now();
                    auto const duration = end_time - start_time;
                    stats.total_time += duration;
                    delete state;
                }
            };

            size_t submitted{}; // Number of requests submitted, always
                                // incremented
            size_t completed{}; // Number of requests completed

            auto rnd = monad::thread_local_prng();
            std::uniform_int_distribution<size_t> dist(
                0, keys.size() ? keys.size() - 1 : 0);
            while (!g_done) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);
                auto const version_bytes =
                    serialize_as_big_endian<sizeof(uint64_t)>(version);

                for (size_t k = 0; k < num_nodes_per_version; ++k) {
                    auto *state = new auto(monad::async::connect(
                        monad::mpt::make_get_sender(
                            async_ctx.get(), keys[dist(rnd)], version),
                        receiver_t{
                            &completed,
                            &ro_db,
                            std::ref(thread_stats),
                            version,
                            version_bytes,
                            std::chrono::steady_clock::now()}));
                    state->initiate();
                    ++submitted;
                }
                if (submitted - completed >= num_async_reads_inflight) {
                    constexpr size_t MAX_TRIEDB_ASYNC_POLLS{300'000};
                    size_t poll_count{0};
                    while (submitted - completed >= num_async_reads_inflight &&
                           poll_count < MAX_TRIEDB_ASYNC_POLLS) {
                        ro_db.poll(true, std::numeric_limits<size_t>::max());
                        ++poll_count;
                    }
                }
            }

            // Finish all enqueued async reads
            while (submitted != completed) {
                ro_db.poll(true, std::numeric_limits<size_t>::max());
            }

            std::ostringstream oss;
            oss << "Async reader thread (0x" << std::hex
                << std::this_thread::get_id() << std::dec << ") finished"
                << ". Did " << thread_stats.nsuccess << " successful and "
                << thread_stats.nfailed << " failed reads" << std::endl;
            std::cout << oss.str();

            auto lock = std::lock_guard<std::mutex>(total_stats.mutex);
            total_stats.lookup.num +=
                thread_stats.nsuccess + thread_stats.nfailed;
            total_stats.lookup.time += thread_stats.total_time;
        };

        auto random_traverse = [&]() {
            ReadOnlyOnDiskDbConfig const ro_config{
                .dbname_paths = {dbname_paths}};
            AsyncIOContext io_ctx{ro_config};
            Db ro_db{io_ctx};

            unsigned nsuccess = 0;
            unsigned nfailed = 0;

            while (ro_db.get_latest_version() == INVALID_BLOCK_NUM && !g_done) {
            }
            // now the first version is written to db
            MONAD_ASSERT(ro_db.get_latest_version() != INVALID_BLOCK_NUM);
            MONAD_ASSERT(ro_db.get_earliest_version() != INVALID_BLOCK_NUM);

            struct VersionValidatorMachine : public TraverseMachine
            {
                Nibbles path{};
                size_t num_nodes;
                sig_atomic_t volatile &done;

                explicit VersionValidatorMachine(
                    size_t num_nodes_, sig_atomic_t volatile &done_)
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
                    return !g_done;
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

            auto start = std::chrono::steady_clock::now();

            auto rnd = monad::thread_local_prng();
            while (!g_done) {
                auto const version = select_rand_version(ro_db, rnd, prng_bias);
                if (auto cursor = ro_db.find(prefix, version);
                    cursor.has_value()) {
                    VersionValidatorMachine machine(
                        num_nodes_per_version, g_done);
                    machine.num_nodes = num_nodes_per_version;
                    if (!ro_db.traverse(cursor.value(), machine, version)) {
                        auto const min_version = ro_db.get_earliest_version();
                        MONAD_ASSERT(version < min_version);
                        ++nfailed;
                    }
                    else {
                        ++nsuccess;
                    }
                }
                else {
                    auto const min_version = ro_db.get_earliest_version();
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

            auto lock = std::lock_guard<std::mutex>(total_stats.mutex);
            total_stats.traverse.num += nsuccess + nfailed;
            total_stats.traverse.time +=
                std::chrono::steady_clock::now() - start;
        };

        std::cout << "Running read only DB benchmark..." << std::endl;

        std::vector<std::thread> readers;
        for (unsigned i = 0; i < num_async_reader_threads; ++i) {
            readers.emplace_back(random_async_read);
        }

        for (unsigned i = 0; i < num_traverse_threads; ++i) {
            readers.emplace_back(random_traverse);
        }

        alarm(runtime_seconds);
        while (!g_done) {
            ++version;
            upsert_new_version(version);
            std::this_thread::sleep_for(
                std::chrono::milliseconds(update_delay_ms));
        }
        for (auto &t : readers) {
            t.join();
        }

        std::cout << "Writer finished. Max version in RWDb is "
                  << rw_db.get_latest_version() << ", min version in RWDb is "
                  << rw_db.get_earliest_version() << "\n\n";

        std::cout << "Total stats:\n";
        std::cout
            << "  Total lookups: " << total_stats.lookup.num
            << "\n   Lookups per second: "
            << total_stats.lookup.num / runtime_seconds
            << "\n  Lookup latency (us): "
            << (total_stats.lookup.num != 0
                    ? std::chrono::duration_cast<std::chrono::microseconds>(
                          total_stats.lookup.time)
                              .count() /
                          (int64_t)total_stats.lookup.num
                    : 0)
            << "\n Total traversals: " << total_stats.traverse.num
            << "\n   Traversals per second: "
            << total_stats.traverse.num / runtime_seconds
            << "\n  Traversal latency (us): "
            << (total_stats.traverse.num != 0
                    ? std::chrono::duration_cast<std::chrono::microseconds>(
                          total_stats.traverse.time)
                              .count() /
                          (int64_t)total_stats.traverse.num
                    : 0)
            << std::endl;
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
