#include <CLI/CLI.hpp>

#include "test_fixtures_base.hpp"

#include <monad/async/config.hpp>
#include <monad/async/connected_operation.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/io.hpp>
#include <monad/async/io_senders.hpp>
#include <monad/async/storage_pool.hpp>
#include <monad/core/array.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.h>
#include <monad/core/scope_polyfill.hpp>
#include <monad/core/small_prng.hpp>
#include <monad/core/unordered_map.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>
#include <monad/mpt/detail/boost_fiber_workarounds.hpp>
#include <monad/mpt/find_request_sender.hpp>
#include <monad/mpt/nibbles_view.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/state_machine.hpp>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>
#include <monad/mpt/util.hpp>

#include <boost/fiber/fiber.hpp>
#include <boost/fiber/operations.hpp>

#include <quill/Quill.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cassert>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <csignal>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <random>
#include <stdexcept>
#include <string>
#include <system_error>
#include <thread>
#include <tuple>
#include <utility>
#include <vector>

#include <linux/fs.h>

#undef BLOCK_SIZE // without this concurrentqueue.h gets sad
#include "concurrentqueue.h"

template <class T>
using concurrent_queue = moodycamel::ConcurrentQueue<T>;

#include <fcntl.h>
#include <linux/fs.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/syscall.h> // for SYS_gettid
#include <unistd.h> // for syscall()

#define SLICE_LEN 100000
#define MAX_NUM_KEYS 250000000

using namespace monad::mpt;

static void ctrl_c_handler(int s)
{
    (void)s;
    exit(0);
}

void __print_bytes_in_hex(monad::byte_string_view arr)
{
    fprintf(stdout, "0x");
    for (auto const &c : arr) {
        fprintf(stdout, "%02x", (uint8_t)c);
    }
    fprintf(stdout, "\n");
}

namespace
{
    constexpr unsigned char state_nibble = 0;
    auto const state_nibbles = concat(state_nibble);
    constexpr auto prefix_len = 1;
}

/*  Commit one batch of updates
    key_offset: insert key starting from this number
    nkeys: number of keys to insert in this batch
*/
Node::UniquePtr batch_upsert_commit(
    std::ostream &csv_writer, uint64_t block_id, uint64_t const vec_idx,
    uint64_t const key_offset, uint64_t const nkeys,
    std::vector<monad::byte_string> &keccak_keys,
    std::vector<monad::byte_string> &keccak_values, bool const erase,
    bool compaction, Node::UniquePtr prev_root, UpdateAuxImpl &aux,
    StateMachine &sm)
{

    std::vector<Update> update_alloc;
    update_alloc.reserve(SLICE_LEN);
    UpdateList state_updates;
    for (uint64_t i = 0; i < nkeys; ++i) {
        state_updates.push_front(update_alloc.emplace_back(
            erase ? make_erase(keccak_keys[i + vec_idx])
                  : make_update(
                        keccak_keys[i + vec_idx],
                        keccak_values[i + vec_idx],
                        false,
                        UpdateList{},
                        block_id)));
    }

    UpdateList updates;
    Update top_update = make_update(
        state_nibbles,
        monad::byte_string_view{},
        false,
        std::move(state_updates),
        block_id);
    updates.push_front(top_update);

    auto ts_before = std::chrono::steady_clock::now();
    auto new_root = aux.do_update(
        std::move(prev_root), sm, std::move(updates), block_id, compaction);
    auto ts_after = std::chrono::steady_clock::now();
    double const tm_ram =
        static_cast<double>(
            std::chrono::duration_cast<std::chrono::nanoseconds>(
                ts_after - ts_before)
                .count()) /
        1000000000.0;

    fprintf(stdout, "root->data : ");
    MONAD_ASSERT(new_root->next(0) != nullptr);
    MONAD_ASSERT(new_root->next(0)->number_of_children() > 1);
    __print_bytes_in_hex(new_root->next(0)->data());

    fprintf(
        stdout,
        "next_key_id: %lu, nkeys upserted: %lu, upsert+commit in RAM: %f "
        "/s, total_t %.4f s",
        (key_offset + vec_idx + nkeys) % MAX_NUM_KEYS,
        nkeys,
        (double)nkeys / tm_ram,
        tm_ram);
    if (aux.is_on_disk()) {
        fprintf(stdout, ", max creads %u", aux.io->max_reads_in_flight());
        aux.io->reset_records();
    }
    fprintf(stdout, "\n=====\n");
    fflush(stdout);

    if (csv_writer) {
        csv_writer << (key_offset + vec_idx + nkeys) << ","
                   << ((double)nkeys / tm_ram) << std::endl;
    }

    return new_root;
}

void prepare_keccak(
    size_t nkeys, std::vector<monad::byte_string> &keccak_keys,
    std::vector<monad::byte_string> &keccak_values, size_t key_offset,
    bool realistic_corpus, bool is_random)
{
    size_t val;
    // prepare keccak
    if (realistic_corpus) {
        /* We know from analysing Ethereum chain history that:

        - Under 2% of all accounts are recipients of 65% of all transactions.
        - Under 5% of all accounts are recipients of 75% of all transactions.
        - Around one third of all accounts are recipients of 90% of all
        transactions.
        - Around two thirds of all accounts are recipients of 95% of all
        transactions.

        Or put another way:
        - One third of all accounts are recipients of 5% of all transactions.
        - Two thirds of all accounts are recipients of 10% of all transactions.
        - 95% of all accounts are recipients of 25% of all transactions.
        - 98% of all accounts are recipients of 35% of all transactions.
        - So just under 2% of all accounts are recipients of two thirds of all
        transactions.
        */
        static constexpr auto MULTIPLIER = 3.7;
        static auto const DIVISOR = pow(MULTIPLIER, MULTIPLIER);
        static constexpr uint32_t TOTAL_KEYS = 500000000;
        static double const MAX_RAND = double(monad::small_prng::max());
        monad::small_prng rand(uint32_t(key_offset / (100 * SLICE_LEN)));
        monad::unordered_flat_set<uint32_t> seen;
        for (size_t i = 0; i < nkeys; ++i) {
            if ((i % SLICE_LEN) == 0) {
                seen.clear();
            }
            for (;;) {
                double r = double(rand()) / MAX_RAND;
                r = pow(MULTIPLIER, MULTIPLIER * r) / DIVISOR;
                uint32_t j = uint32_t(double(TOTAL_KEYS) * r);
                if (!seen.contains(j)) {
                    seen.insert(j);
                    keccak_keys[i].resize(32);
                    keccak256(
                        (unsigned char const *)&j, 4, keccak_keys[i].data());

                    val = (i + key_offset) * 2;
                    keccak_values[i].resize(32);
                    keccak256(
                        (unsigned char const *)&val,
                        8,
                        keccak_values[i].data());
                    break;
                }
            }
        }
    }
    else if (is_random) {
        std::random_device rd; // a seed source for the random number engine
        std::mt19937 gen(rd()); // mersenne_twister_engine seeded with rd()
        std::uniform_int_distribution<> distrib(0, MAX_NUM_KEYS - 1);
        MONAD_ASSERT(distrib.min() == 0 && distrib.max() == MAX_NUM_KEYS - 1);

        size_t key;
        monad::unordered_flat_set<size_t> keys_per_slice; // dedup
        // prepare keccak
        for (size_t i = 0; i < nkeys; ++i) {
            if (i % SLICE_LEN == 0) {
                keys_per_slice.clear();
            }
            do {
                key = (size_t)distrib(gen);
            }
            while (keys_per_slice.find(key) != keys_per_slice.end());
            keys_per_slice.insert(key);
            keccak_keys[i].resize(32);
            keccak256((unsigned char const *)&key, 8, keccak_keys[i].data());
            val = key * 2;
            keccak_values[i].resize(32);
            keccak256((unsigned char const *)&val, 8, keccak_values[i].data());
        }
    }
    else {
        size_t key;
        for (size_t i = 0; i < nkeys; ++i) {
            key = (i + key_offset) % MAX_NUM_KEYS;
            keccak_keys[i].resize(32);
            keccak256((unsigned char const *)&key, 8, keccak_keys[i].data());
            val = key * 2;
            keccak_values[i].resize(32);
            keccak256((unsigned char const *)&val, 8, keccak_values[i].data());
        }
    }
}

int main(int argc, char *argv[])
{
    struct sigaction sig;
    sig.sa_handler = &ctrl_c_handler;
    sigemptyset(&sig.sa_mask);
    sig.sa_flags = 0;
    sigaction(SIGINT, &sig, nullptr);

    unsigned n_slices = 20;
    bool append = false;
    std::vector<std::filesystem::path> dbname_paths;
    std::filesystem::path csv_stats_path;
    uint64_t key_offset = 0;
    unsigned sq_thread_cpu = 15;
    bool erase = false;
    bool in_memory = false; // default is on disk
    bool empty_cpu_caches = false;
    bool realistic_corpus = false;
    bool random_keys = false;
    bool compaction = false;
    bool use_iopoll = false;
    int file_size_db = 512; // truncate to 512 gb by default
    unsigned random_read_benchmark_threads = 0;
    unsigned concurrent_read_io_limit = 0;
    uint64_t history_len = 100;

    struct runtime_reconfig_t
    {
        std::filesystem::path path;
        std::chrono::steady_clock::time_point last_parsed;

        unsigned concurrent_read_io_limit = 0;

    } runtime_reconfig;

    CLI::App cli{"monad_merge_trie_test"};
    try {
        printf("main() runs on tid %ld\n", syscall(SYS_gettid));
        cli.add_flag(
            "--append", append, "append to the latest block in existing db");
        cli.add_option(
            "--db-names",
            dbname_paths,
            "db file names, can have more than one");
        cli.add_option("--csv-stats", csv_stats_path, "CSV stats file name");
        cli.add_option(
            "--key-offset", key_offset, "integer offset to start insert");
        cli.add_option("-n", n_slices, "n batch updates");
        cli.add_option("--kcpu", sq_thread_cpu, "io_uring sq_thread_cpu");
        cli.add_flag("--erase", erase, "test erase");
        auto *is_inmemory = cli.add_flag(
            "--in-memory", in_memory, "config trie to in memory or on-disk");
        cli.add_flag(
            "--empty-cpu-caches",
            empty_cpu_caches,
            "empty cpu caches between updates");
        cli.add_flag(
            "--realistic-corpus",
            realistic_corpus,
            "use test corpus resembling historical patterns");
        cli.add_flag(
            "--random-keys", random_keys, "generate random integers as keys");
        cli.add_flag("--compaction", compaction, "perform compaction on disk");
        cli.add_flag("--use-iopoll", use_iopoll, "use i/o polling in io_uring");
        cli.add_option(
            "--file-size-gb",
            file_size_db,
            "size to create file to if not already exist, only apply to file "
            "not blkdev");
        cli.add_option(
            "--random-read-benchmark",
            random_read_benchmark_threads,
            "how many threads with which to do random reads of the written "
            "database after the write test ends (default is run no test)");
        cli.add_option(
            "--concurrent-read-io-limit",
            concurrent_read_io_limit,
            "the maximum number of concurrent reads to perform at a time "
            "(default is no limit)");
        cli.add_option(
            "--runtime-reconfig-file",
            runtime_reconfig.path,
            "a file to parse every five seconds to adjust config as test runs");
        cli.add_option(
               "--history", history_len, "Initialize disk db history length")
            ->excludes(is_inmemory);
        cli.parse(argc, argv);

        MONAD_ASSERT(in_memory + append < 2);
        if (in_memory && compaction) {
            throw std::invalid_argument(
                "Invalid to init with compaction on in-memory triedb.");
        }
        if (realistic_corpus) {
            random_keys = false;
        }

        std::ofstream csv_writer;
        if (!csv_stats_path.empty()) {
            csv_writer.open(csv_stats_path);
            csv_writer.exceptions(std::ios::failbit | std::ios::badbit);
            csv_writer << "\"Keys written\",\"Per second\"\n";
        }

        quill::start(true);

        /* This does a good job of emptying the CPU's data caches and
        data TLB. It does not empty instruction caches nor instruction TLB,
        including the branch prediction history.
        */
        struct cpu_cache_emptier_t
        {
            enum : size_t
            {
                TLB_ENTRIES = 4096
            };

            std::vector<std::byte *> pages;
            ::monad::small_prng rand;

            explicit cpu_cache_emptier_t(bool enable)
            {
                if (enable) {
                    pages.resize(TLB_ENTRIES);
                    for (size_t n = 0; n < TLB_ENTRIES; n++) {
                        pages[n] = (std::byte *)::mmap(
                            nullptr,
                            4096,
                            PROT_READ | PROT_WRITE,
                            MAP_PRIVATE | MAP_ANONYMOUS | MAP_POPULATE,
                            -1,
                            0);
                        *pages[n] = std::byte(1);
                    }
                }
            }

            ~cpu_cache_emptier_t()
            {
                for (auto *p : pages) {
                    ::munmap(p, 4096);
                }
            }

            void operator()()
            {
                for (size_t n = 0; n < pages.size() * 4; n++) {
                    auto const v = rand();
                    auto const idx1 = (v & 0xffff) & (TLB_ENTRIES - 1);
                    auto const idx2 = ((v >> 16) & 0xffff) & (TLB_ENTRIES - 1);
                    if (idx1 != idx2) {
                        memcpy(pages[idx1], pages[idx2], 4096);
                    }
                }
            }
        } cpu_cache_emptier{empty_cpu_caches};

        uint64_t const keccak_cap = 100 * SLICE_LEN;
        auto keccak_keys = std::vector<monad::byte_string>{keccak_cap};
        auto keccak_values = std::vector<monad::byte_string>{keccak_cap};

        if (dbname_paths.empty()) {
            dbname_paths.emplace_back("test.db");
        }
        for (auto const &dbname_path : dbname_paths) {
            if (!std::filesystem::exists(dbname_path)) {
                int const fd = ::open(
                    dbname_path.c_str(), O_CREAT | O_RDWR | O_CLOEXEC, 0600);
                if (-1 == fd) {
                    throw std::system_error(errno, std::system_category());
                }
                auto unfd =
                    monad::make_scope_exit([fd]() noexcept { ::close(fd); });
                if (-1 ==
                    ::ftruncate(
                        fd,
                        (int64_t)file_size_db * 1024 * 1024 * 1024 + 24576)) {
                    throw std::system_error(errno, std::system_category());
                }
            }
        }

        { /* upsert test begin */
            MONAD_ASYNC_NAMESPACE::storage_pool pool{
                {dbname_paths},
                append
                    ? MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing
                    : MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate};

            // init uring
            monad::io::Ring ring1({512, use_iopoll, sq_thread_cpu});
            monad::io::Ring ring2(
                16
                /* max concurrent write buffers in use <= 6 */
            );

            // init buffer
            monad::io::Buffers rwbuf = make_buffers_for_segregated_read_write(
                ring1,
                ring2,
                8192 * 16,
                16, /* max concurrent write buffers in use <= 6 */
                MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);

            auto io = MONAD_ASYNC_NAMESPACE::AsyncIO{pool, rwbuf};
            io.set_concurrent_read_io_limit(concurrent_read_io_limit);
            auto check_runtime_reconfig = [&] {
                auto const now = std::chrono::steady_clock::now();
                if (now - runtime_reconfig.last_parsed >
                    std::chrono::seconds(5)) {
                    runtime_reconfig.last_parsed = now;
                    if (std::filesystem::exists(runtime_reconfig.path)) {
                        std::ifstream s(runtime_reconfig.path);
                        std::string key;
                        std::string equals;
                        while (!s.eof()) {
                            s >> key >> equals;
                            if (equals == "=") {
                                if (key == "concurrent_read_io_limit") {
                                    s >> runtime_reconfig
                                             .concurrent_read_io_limit;
                                    if (runtime_reconfig
                                            .concurrent_read_io_limit !=
                                        concurrent_read_io_limit) {
                                        concurrent_read_io_limit =
                                            runtime_reconfig
                                                .concurrent_read_io_limit;
                                        io.set_concurrent_read_io_limit(
                                            concurrent_read_io_limit);
                                        std::cout
                                            << "concurrent_read_io_limit = "
                                            << concurrent_read_io_limit
                                            << std::endl;
                                    }
                                }
                                else {
                                    std::cerr << "WARNING: File "
                                              << runtime_reconfig.path
                                              << " had unknown key '" << key
                                              << "'." << std::endl;
                                }
                            }
                        }
                    }
                }
            };

            auto aux =
                in_memory ? UpdateAux<>() : UpdateAux<>(&io, history_len);
            monad::test::StateMachineMerkleWithPrefix<prefix_len> sm{};

            Node::UniquePtr root{};
            if (append) {
                root = read_node_blocking(
                    aux,
                    aux.get_latest_root_offset(),
                    aux.db_history_max_version());
            }
            auto block_id = in_memory ? 0 : (aux.db_history_max_version() + 1);
            printf("starting block id %lu\n", block_id);

            auto begin_test = std::chrono::steady_clock::now();
            uint64_t const max_key = n_slices * SLICE_LEN + key_offset;
            /* start profiling upsert and commit */
            for (uint64_t iter = 0; iter < n_slices; ++iter) {
                check_runtime_reconfig();
                // renew keccak values
                if (!(iter * SLICE_LEN % keccak_cap)) {
                    auto begin_prepare_keccak =
                        std::chrono::steady_clock::now();
                    if (iter) {
                        key_offset += keccak_cap;
                    }
                    // pre-calculate keccak
                    prepare_keccak(
                        std::min(keccak_cap, max_key - key_offset),
                        keccak_keys,
                        keccak_values,
                        key_offset,
                        realistic_corpus,
                        random_keys);
                    fprintf(
                        stdout,
                        "Finish preparing keccak.\nStart transactions\n");
                    fflush(stdout);
                    auto end_prepare_keccak = std::chrono::steady_clock::now();
                    begin_test += end_prepare_keccak - begin_prepare_keccak;
                }

                cpu_cache_emptier();
                root = batch_upsert_commit(
                    csv_writer,
                    block_id++,
                    (iter % 100) * SLICE_LEN, /* vec_idx */
                    key_offset, /* key offset */
                    SLICE_LEN, /* nkeys */
                    keccak_keys,
                    keccak_values,
                    false,
                    compaction,
                    std::move(root),
                    aux,
                    sm);

                if (erase && (iter & 1) != 0) {
                    fprintf(stdout, "> erase iter = %lu\n", iter);
                    fflush(stdout);
                    root = batch_upsert_commit(
                        csv_writer,
                        block_id++,
                        (iter % 100) * SLICE_LEN, /* vec_idx */
                        key_offset, /* key offset */
                        SLICE_LEN, /* nkeys */
                        keccak_keys,
                        keccak_values,
                        true,
                        compaction,
                        std::move(root),
                        aux,
                        sm);

                    fprintf(stdout, "> dup batch iter = %lu\n", iter);

                    root = batch_upsert_commit(
                        csv_writer,
                        block_id++,
                        (iter % 100) * SLICE_LEN, /* vec_idx */
                        key_offset, /* key offset */
                        SLICE_LEN, /* nkeys */
                        keccak_keys,
                        keccak_values,
                        false,
                        compaction,
                        std::move(root),
                        aux,
                        sm);
                }
            }

            auto end_test = std::chrono::steady_clock::now();
            auto test_secs =
                static_cast<double>(
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        end_test - begin_test)
                        .count()) /
                1000000.0;
            uint64_t bytes_used = 0;
            for (auto const &device : pool.devices()) {
                bytes_used += device.capacity().second;
            }
            printf(
                "\nTotal test time: %f secs. Total storage consumed: %f Gb\n",
                test_secs,
                double(bytes_used) / 1024.0 / 1024.0 / 1024.0);
            if (csv_writer) {
                csv_writer << "\n\"Total test time:\"," << test_secs;
                csv_writer << "\n\"Total storage consumed:\"," << bytes_used
                           << std::endl;
            }
        } /* upsert test end */

        if (random_read_benchmark_threads > 0) {
            using find_bytes_request_sender =
                find_request_sender<monad::byte_string>;
            {
                auto begin = std::chrono::steady_clock::now();
                while (std::chrono::steady_clock::now() - begin <
                       std::chrono::seconds(1)) {
                }
            }
            // read only
            // init uring
            monad::io::Ring ring({512, use_iopoll, sq_thread_cpu});

            // init buffer
            monad::io::Buffers rwbuf = make_buffers_for_read_only(
                ring,
                8192 * 16,
                MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);

            MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flag{};
            flag.open_read_only = true;
            MONAD_ASYNC_NAMESPACE::storage_pool pool{
                {dbname_paths},
                MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing,
                flag};
            auto io = MONAD_ASYNC_NAMESPACE::AsyncIO{pool, rwbuf};
            io.set_concurrent_read_io_limit(concurrent_read_io_limit);

            auto load_db = [&] {
                auto ret = std::make_unique<
                    std::tuple<UpdateAux<>, Node::UniquePtr, NodeCursor>>();
                UpdateAux<> &aux = std::get<0>(*ret);
                Node::UniquePtr &root = std::get<1>(*ret);
                NodeCursor &state_start = std::get<2>(*ret);
                if (!in_memory) {
                    aux.set_io(&io, history_len);
                }
                root = read_node_blocking(
                    aux,
                    aux.get_latest_root_offset(),
                    aux.db_history_max_version());
                auto [res, errc] = find_blocking(
                    aux, *root, state_nibbles, aux.db_history_max_version());
                MONAD_ASSERT(errc == find_result::success);
                state_start = res;
                return ret;
            };
            {
                auto db = load_db();
                UpdateAux<> &aux = std::get<0>(*db);
                NodeCursor const state_start = std::get<2>(*db);
                printf(
                    "\n********************************************************"
                    "*"
                    "*****\n\nDoing random read benchmark with %u concurrent "
                    "senders "
                    "on a single thread for ten seconds ...\n",
                    random_read_benchmark_threads);

                struct receiver_t
                {
                    uint64_t &ops;
                    bool &done;
                    unsigned const n_slices;
                    find_bytes_request_sender *sender{nullptr};
                    NodeCursor state_start;
                    monad::small_prng rand;
                    monad::byte_string key;

                    explicit receiver_t(
                        uint64_t &ops_, bool &done_, unsigned n_slices_,
                        NodeCursor begin, uint32_t id)
                        : ops(ops_)
                        , done(done_)
                        , n_slices(n_slices_)
                        , state_start(begin)
                        , rand(id)
                        , key(32, 0)
                    {
                    }

                    void set_value(
                        MONAD_ASYNC_NAMESPACE::erased_connected_operation
                            *io_state,
                        find_bytes_request_sender::result_type res)
                    {
                        MONAD_ASSERT(res);
                        auto const [data, errc] = res.assume_value();
                        MONAD_ASSERT(
                            data.size() == KECCAK256_SIZE || data.size() == 0);
                        MONAD_ASSERT(errc == monad::mpt::find_result::success);
                        ops++;

                        if (!done) {
                            size_t key_src = (rand() % (n_slices * SLICE_LEN));
                            keccak256(
                                (unsigned char const *)&key_src, 8, key.data());
                            sender->reset(state_start, key);
                            io_state->initiate();
                        }
                    }
                };

                using connected_state_type = MONAD_ASYNC_NAMESPACE::
                    connected_operation<find_bytes_request_sender, receiver_t>;

                uint64_t ops{0};
                bool signal_done{false};
                inflight_node_t inflights;
                std::vector<std::unique_ptr<connected_state_type>> states;
                states.reserve(random_read_benchmark_threads);
                for (uint32_t n = 0; n < random_read_benchmark_threads; n++) {
                    states.emplace_back(new auto(connect(
                        *aux.io,
                        find_bytes_request_sender{
                            aux,
                            inflights,
                            state_start,
                            NibblesView{},
                            true,
                            5},
                        receiver_t(
                            ops, signal_done, n_slices, state_start, n))));
                }

                // Initiate
                for (auto &state : states) {
                    state->receiver().sender = &state->sender();
                    state->receiver().set_value(
                        state.get(),
                        monad::mpt::find_result_type<monad::byte_string>(
                            {}, monad::mpt::find_result::success));
                }

                auto begin = std::chrono::steady_clock::now();
                while (std::chrono::steady_clock::now() - begin <
                       std::chrono::seconds(10)) {
                    aux.io->poll_nonblocking(1);
                }
                auto end = std::chrono::steady_clock::now();
                auto diff =
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        end - begin);
                printf(
                    "   Did %f random reads per second.\n",
                    1000000.0 * double(ops) / double(diff.count()));
                signal_done = true;
                aux.io->wait_until_done();
            }

            {
                auto db = load_db();
                UpdateAux<> &aux = std::get<0>(*db);
                NodeCursor const state_start = std::get<2>(*db);
                printf(
                    "\n********************************************************"
                    "*"
                    "*****\n\nDoing random read benchmark with %u fibers "
                    "on a single thread for ten seconds ...\n",
                    random_read_benchmark_threads);

                uint64_t ops{0};
                bool signal_done{false};
                inflight_map_t inflights;
                auto find = [n_slices, &ops, &signal_done, &inflights](
                                UpdateAuxImpl *aux,
                                NodeCursor state_start,
                                unsigned n) {
                    monad::small_prng rand(n);
                    monad::byte_string key;
                    key.resize(32);
                    while (!signal_done) {
                        size_t key_src = (rand() % (n_slices * SLICE_LEN));
                        keccak256(
                            (unsigned char const *)&key_src, 8, key.data());

                        monad::threadsafe_boost_fibers_promise<
                            monad::mpt::find_cursor_result_type>
                            promise;
                        find_notify_fiber_future(
                            *aux, inflights, promise, state_start, key);
                        auto const [node_cursor, errc] =
                            promise.get_future().get();
                        MONAD_ASSERT(node_cursor.is_valid());
                        MONAD_ASSERT(errc == monad::mpt::find_result::success);
                        MONAD_ASSERT(node_cursor.node->has_value());
                        ops++;
                        boost::this_fiber::yield();
                    }
                };
                auto poll =
                    [&signal_done](MONAD_ASYNC_NAMESPACE::AsyncIO *const io) {
                        while (!signal_done) {
                            io->poll_nonblocking(1);
                            boost::this_fiber::yield();
                        }
                    };

                std::vector<boost::fibers::fiber> fibers;
                fibers.reserve(random_read_benchmark_threads);
                for (unsigned n = 0; n < random_read_benchmark_threads; n++) {
                    fibers.emplace_back(find, &aux, state_start, n);
                }
                boost::fibers::fiber poll_fiber(poll, aux.io);
                auto begin = std::chrono::steady_clock::now();
                do {
                    boost::this_fiber::yield();
                }
                while (std::chrono::steady_clock::now() - begin <
                       std::chrono::seconds(10));
                auto end = std::chrono::steady_clock::now();
                auto diff =
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        end - begin);
                printf(
                    "   Did %f random reads per second.\n",
                    1000000.0 * double(ops) / double(diff.count()));
                fflush(stdout);
                signal_done = true;
                for (auto &fiber : fibers) {
                    io.wait_until_done();
                    fiber.join();
                }
                poll_fiber.join();
            }

            {
                auto db = load_db();
                UpdateAux<> &aux = std::get<0>(*db);
                NodeCursor const state_start = std::get<2>(*db);
                printf(
                    "\n********************************************************"
                    "*"
                    "*****\n\nDoing random read benchmark with a fiber "
                    "on %u threads using a concurrent queue for "
                    "synchronisation for ten seconds ...\n",
                    random_read_benchmark_threads);

                std::atomic<uint64_t> ops{0};
                std::atomic<int> signal_done{0};
                concurrent_queue<fiber_find_request_t> req;
                auto find = [n_slices, &ops, &signal_done, &req](
                                NodeCursor const state_start, unsigned n) {
                    monad::small_prng rand(n);
                    monad::byte_string key;
                    key.resize(32);
                    // We need to keep these around as destructing them when
                    // another thread is still using them is apparently not
                    // allowed in Boost.Fiber
                    std::array<
                        monad::threadsafe_boost_fibers_promise<
                            monad::mpt::find_cursor_result_type>,
                        4>
                        promises;
                    auto *promise_it = promises.begin();
                    while (0 == signal_done.load(std::memory_order_relaxed)) {
                        size_t key_src = (rand() % (n_slices * SLICE_LEN));
                        keccak256(
                            (unsigned char const *)&key_src, 8, key.data());

                        if (promise_it == promises.end()) {
                            promise_it = promises.begin();
                        }
                        fiber_find_request_t const request{
                            .promise = &*promise_it++,
                            .start = state_start,
                            .key = key};
                        request.promise->reset();
                        req.enqueue(request);
                        auto const [node_cursor, errc] =
                            request.promise->get_future().get();
                        MONAD_ASSERT(node_cursor.is_valid());
                        MONAD_ASSERT(errc == monad::mpt::find_result::success);
                        MONAD_ASSERT(node_cursor.node->has_value());
                        ops.fetch_add(1, std::memory_order_relaxed);
                    }
                    signal_done.fetch_add(1, std::memory_order_relaxed);
                    while (signal_done.load(std::memory_order_relaxed) > 0) {
                        std::this_thread::yield();
                    }
                };

                auto poll = [&signal_done, &req](UpdateAuxImpl *aux) {
                    inflight_map_t inflights;
                    fiber_find_request_t request;
                    for (;;) {
                        boost::this_fiber::yield();
                        if (0 == signal_done.load(std::memory_order_relaxed)) {
                            aux->io->poll_nonblocking(1);
                        }
                        else {
                            aux->io->wait_until_done();
                            return;
                        }
                        if (req.try_dequeue(request)) {
                            find_notify_fiber_future(
                                *aux,
                                inflights,
                                *request.promise,
                                request.start,
                                request.key);
                        }
                    }
                };

                std::vector<std::thread> threads;
                threads.reserve(random_read_benchmark_threads);
                for (unsigned n = 0; n < random_read_benchmark_threads; n++) {
                    threads.emplace_back(find, state_start, n);
                }
                boost::fibers::fiber poll_fiber(poll, &aux);
                auto begin = std::chrono::steady_clock::now();
                do {
                    boost::this_fiber::yield();
                }
                while (std::chrono::steady_clock::now() - begin <
                       std::chrono::seconds(10));
                auto end = std::chrono::steady_clock::now();
                auto diff =
                    std::chrono::duration_cast<std::chrono::microseconds>(
                        end - begin);
                printf(
                    "   Did %f random reads per second.\n",
                    1000000.0 * double(ops) / double(diff.count()));
                signal_done = 1;
                std::cout << "   Joining threads 1 ..." << std::endl;
                while (signal_done < int(random_read_benchmark_threads + 1)) {
                    boost::this_fiber::yield();
                    inflight_map_t inflights;
                    fiber_find_request_t request;
                    if (req.try_dequeue(request)) {
                        find_notify_fiber_future(
                            aux,
                            inflights,
                            *request.promise,
                            request.start,
                            request.key);
                    }
                }
                std::cout << "   Joining threads 2 ..." << std::endl;
                signal_done = -1;
                for (auto &thread : threads) {
                    thread.join();
                }
                std::cout << "   Joining poll fiber ..." << std::endl;
                poll_fiber.join();
                std::cout << "   Done!" << std::endl;
            }
        }
    }

    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
    }

    catch (std::exception const &e) {
        std::cerr << "FATAL: " << e.what() << std::endl;
        return 1;
    }

    return 0;
}
