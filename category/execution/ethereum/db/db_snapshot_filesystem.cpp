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
#include <category/core/blake3.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/db/db_snapshot.h>
#include <category/execution/ethereum/db/db_snapshot_filesystem.h>
#include <category/execution/ethereum/db/db_snapshot_internal.hpp>

#include <ankerl/unordered_dense.h>
#include <blake3.h>

#include <tbb/concurrent_queue.h>
#include <tbb/parallel_for.h>
#include <tbb/task_arena.h>

#include <algorithm>
#include <cerrno>
#include <cstddef>
#include <cstring>
#include <exception>
#include <fcntl.h>
#include <filesystem>
#include <format>
#include <fstream>
#include <memory>
#include <thread>
#include <unistd.h>
#include <utility>
#include <vector>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct SnapshotShardStream
{
    std::ofstream foutput;
    // The checksum is written once, at destroy time, so only its path is kept
    // here and the stream is opened lazily rather than held open for the whole
    // dump. The data stream (foutput) is already held open per shard across all
    // 256 shards; keeping the checksum stream open too would double that fd
    // footprint, so deferring it halves the descriptors the dump holds at once.
    std::filesystem::path checksum_path;
    blake3_hasher hasher;
};

using SnapshotShard =
    std::array<SnapshotShardStream, MONAD_SNAPSHOT_FILES_PER_SHARD>;

MONAD_ANONYMOUS_NAMESPACE_END

struct monad_db_snapshot_filesystem_write_user_context
{
    std::filesystem::path root;
    ankerl::unordered_dense::map<uint64_t, monad::SnapshotShard> shard;

    explicit monad_db_snapshot_filesystem_write_user_context(
        std::filesystem::path const root)
        : root{root}
    {
    }
};

monad_db_snapshot_filesystem_write_user_context *
monad_db_snapshot_filesystem_write_user_context_create(
    char const *const root, uint64_t const block)
{
    std::filesystem::path const snapshot{
        std::filesystem::path{root} / std::to_string(block)};
    MONAD_ASSERT_PRINTF(
        std::filesystem::create_directories(snapshot),
        "snapshot failed, %s already exists!",
        snapshot.c_str());
    return new monad_db_snapshot_filesystem_write_user_context{snapshot};
}

void monad_db_snapshot_filesystem_write_user_context_destroy(
    monad_db_snapshot_filesystem_write_user_context *const context)
{
    for (auto &[_, stream] : context->shard) {
        for (auto &shard : stream) {
            // Flush and close the data file now, rather than letting the
            // ofstream destructor do it (where the result would be discarded),
            // so a write/flush/close failure -- e.g. ENOSPC on the final
            // buffer, or a deferred write-back error surfaced only at close()
            // -- aborts here at dump time with the right cause instead of
            // surfacing later as a load-time checksum mismatch on a truncated
            // file.
            errno = 0;
            shard.foutput.close();
            MONAD_ASSERT_PRINTF(
                shard.foutput.good(),
                "failed to write snapshot data file %s: %s",
                std::filesystem::path{shard.checksum_path}
                    .replace_extension()
                    .c_str(),
                std::strerror(errno));

            monad::bytes32_t hash;
            blake3_hasher_finalize(&shard.hasher, hash.bytes, BLAKE3_OUT_LEN);
            errno = 0;
            std::ofstream fchecksum{shard.checksum_path, std::ios::out};
            MONAD_ASSERT_PRINTF(
                fchecksum.is_open(),
                "failed to open %s: %s",
                shard.checksum_path.c_str(),
                std::strerror(errno));
            fchecksum << fmt::format("{}", hash);
            fchecksum.close();
            MONAD_ASSERT_PRINTF(
                fchecksum.good(),
                "failed to write checksum %s: %s",
                shard.checksum_path.c_str(),
                std::strerror(errno));
        }
    }
    delete context;
}

uint64_t monad_db_snapshot_write_filesystem(
    uint64_t const shard, monad_snapshot_type const type,
    unsigned char const *const bytes, size_t const len, void *const user)
{
    auto *const context =
        reinterpret_cast<monad_db_snapshot_filesystem_write_user_context *>(
            user);
    if (MONAD_UNLIKELY(!context->shard.contains(shard))) {
        auto const shard_dir = context->root / std::to_string(shard);
        MONAD_ASSERT(std::filesystem::create_directory(shard_dir));
        auto const [it, success] =
            context->shard.emplace(shard, monad::SnapshotShard{});
        MONAD_ASSERT(success);
        constexpr std::array files = {
            "eth_header", "account", "storage", "code"};
        static_assert(files.size() == MONAD_SNAPSHOT_FILES_PER_SHARD);
        for (size_t i = 0; i < it->second.size(); ++i) {
            auto &[foutput, checksum_path, hasher] = it->second.at(i);
            std::filesystem::path const output = shard_dir / files[i];
            errno = 0;
            foutput.open(output, std::ios::binary | std::ios::out);
            MONAD_ASSERT_PRINTF(
                foutput.is_open(),
                "failed to open %s: %s",
                output.c_str(),
                std::strerror(errno));
            checksum_path = std::format("{}.blake3", output.c_str());
            blake3_hasher_init(&hasher);
        }
    }

    auto &stream = context->shard.at(shard).at(type);
    stream.foutput.write(
        reinterpret_cast<char const *>(bytes),
        static_cast<std::streamsize>(len));
    MONAD_ASSERT(stream.foutput.good());
    blake3_hasher_update(&stream.hasher, bytes, len);
    return len;
}

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Read one snapshot input file into a heap buffer and verify its stored BLAKE3
// checksum. Uses pread rather than mmap: worker threads run this concurrently,
// and per-shard mmap/munmap/madvise serialize on the process mmap_lock, which
// dominates the parallel load with system-time contention. A size-0 file
// returns an empty buffer.
monad::byte_string read_file(std::filesystem::path const &file)
{
    using namespace monad;
    MONAD_ASSERT_PRINTF(
        std::filesystem::is_regular_file(file),
        "snapshot input file missing or not a regular file: %s",
        file.c_str());

    size_t const size = std::filesystem::file_size(file);
    byte_string buf;
    if (size) {
        buf.resize(size);
        errno = 0;
        int const fd = open(file.c_str(), O_RDONLY);
        MONAD_ASSERT_PRINTF(
            fd != -1,
            "failed to open %s: %s",
            file.c_str(),
            std::strerror(errno));
        posix_fadvise(fd, 0, 0, POSIX_FADV_SEQUENTIAL);
        for (size_t off = 0; off < size;) {
            errno = 0;
            ssize_t const n = pread(
                fd, buf.data() + off, size - off, static_cast<off_t>(off));
            MONAD_ASSERT_PRINTF(
                n > 0,
                "failed to read %s: %s",
                file.c_str(),
                std::strerror(errno));
            off += static_cast<size_t>(n);
        }
        close(fd);

        std::filesystem::path const checksum{
            std::format("{}.blake3", file.c_str())};
        MONAD_ASSERT_PRINTF(
            std::filesystem::is_regular_file(checksum),
            "missing checksum file %s",
            checksum.c_str());
        errno = 0;
        std::ifstream t(checksum);
        MONAD_ASSERT_PRINTF(
            t.is_open(),
            "failed to open checksum file %s: %s",
            checksum.c_str(),
            std::strerror(errno));
        std::stringstream buffer;
        buffer << t.rdbuf();
        auto const stored_hash = from_hex<bytes32_t>(buffer.str());
        auto const calculated_hash = to_bytes(blake3(buf));
        MONAD_ASSERT_PRINTF(
            stored_hash == calculated_hash,
            "calculated checksum does not match stored checksum for file %s",
            file.c_str());
    }
    return buf;
}

// Pure-CPU shard prep: read the 4 files into buffers owned by the result, then
// build the shard's Updates from views into those buffers so they outlive the
// consumer's upsert. Called from worker threads. The eth_header buffer is only
// needed transiently (fill_prepared_shard copies it into ps->eth_header).
std::unique_ptr<monad::PreparedShard> prepare_shard_from_files(
    std::filesystem::path const &dir, uint64_t const shard,
    uint64_t const block, bool const page_encoded)
{
    monad::byte_string const eth_header = read_file(dir / "eth_header");
    auto ps = std::make_unique<monad::PreparedShard>();
    ps->account_bytes = read_file(dir / "account");
    ps->storage_bytes = read_file(dir / "storage");
    ps->code_bytes = read_file(dir / "code");
    fill_prepared_shard(
        *ps,
        shard,
        block,
        page_encoded,
        monad::byte_string_view{eth_header},
        monad::byte_string_view{ps->account_bytes},
        monad::byte_string_view{ps->storage_bytes},
        monad::byte_string_view{ps->code_bytes});
    return ps;
}

MONAD_ANONYMOUS_NAMESPACE_END

void monad_db_snapshot_load_filesystem(
    char const *const *const dbname_paths, size_t const len,
    unsigned const sq_thread_cpu, char const *const snapshot_dir,
    uint64_t const block, bool const load_to_secondary,
    unsigned const concurrency)
{
    std::filesystem::path const root{std::format("{}/{}", snapshot_dir, block)};
    MONAD_ASSERT(std::filesystem::is_directory(root));
    // The input snapshot is always slot-encoded (the standard format produced
    // by monad_db_dump_snapshot from a slot db). If the target timeline is
    // page-encoded, the loader converts slot leaves to page leaves on the fly.
    monad_db_snapshot_loader *const loader = monad_db_snapshot_loader_create(
        block, dbname_paths, len, sq_thread_cpu, load_to_secondary);

    // Read the target encoding once on this thread; the Db is touched only
    // here and by commit_prepared, never by the workers.
    bool const page_encoded = snapshot_loader_page_encoded(loader);

    // The 256 shards are disjoint 2-nibble subtrees, so any commit order yields
    // a bit-identical root.
    std::vector<std::pair<uint64_t, std::filesystem::path>> shards;
    for (auto const &dir : std::filesystem::directory_iterator{root}) {
        shards.emplace_back(std::stoull(dir.path().stem()), dir.path());
    }

    // Prep is a minority of the load (the serial upsert dominates), so a
    // handful of workers keep the single consumer fed; more only inflate
    // resident memory. Cap the auto (0) default rather than grabbing every
    // core. Callers can still request an explicit higher count.
    constexpr unsigned AUTO_WORKERS_CAP = 16;
    unsigned const workers =
        concurrency == 0
            ? std::min(
                  std::max(1u, std::thread::hardware_concurrency()),
                  AUTO_WORKERS_CAP)
            : concurrency;

    if (workers <= 1) {
        for (auto const &[shard, path] : shards) {
            commit_prepared(
                loader,
                monad::prepare_shard_from_files(
                    path, shard, block, page_encoded));
        }
    }
    else {
        // Workers prep shards into a bounded queue; this thread (the sole Db
        // user) commits them. Capacity == workers bounds resident prepped
        // shards to ~2*workers (queued + in-flight). A trailing null pushed
        // after the parallel_for barrier is a poison pill that unblocks the
        // consumer even if a worker aborts.
        tbb::concurrent_bounded_queue<std::unique_ptr<monad::PreparedShard>>
            queue;
        queue.set_capacity(static_cast<std::ptrdiff_t>(workers));

        std::exception_ptr producer_error;
        std::thread producer([&] {
            try {
                tbb::task_arena arena(static_cast<int>(workers));
                arena.execute([&] {
                    tbb::parallel_for(
                        size_t{0}, shards.size(), [&](size_t const i) {
                            queue.push(monad::prepare_shard_from_files(
                                shards[i].second,
                                shards[i].first,
                                block,
                                page_encoded));
                        });
                });
            }
            catch (...) {
                producer_error = std::current_exception();
            }
            queue.push(nullptr);
        });

        while (true) {
            std::unique_ptr<monad::PreparedShard> ps;
            queue.pop(ps);
            if (!ps) {
                break;
            }
            commit_prepared(loader, std::move(ps));
        }
        producer.join();
        if (producer_error) {
            std::rethrow_exception(producer_error);
        }
    }

    monad_db_snapshot_loader_destroy(loader);
}
