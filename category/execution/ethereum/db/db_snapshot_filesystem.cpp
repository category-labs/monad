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

#include <ankerl/unordered_dense.h>
#include <blake3.h>

#include <cerrno>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <format>
#include <fstream>
#include <linux/mman.h>
#include <sys/mman.h>

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

void monad_db_snapshot_load_filesystem(
    char const *const *const dbname_paths, size_t const len,
    unsigned const sq_thread_cpu, char const *const snapshot_dir,
    uint64_t const block, bool const load_to_secondary)
{
    std::filesystem::path const root{std::format("{}/{}", snapshot_dir, block)};
    MONAD_ASSERT(std::filesystem::is_directory(root));
    // The input snapshot is always slot-encoded (the standard format produced
    // by monad_db_dump_snapshot from a slot db). If the target timeline is
    // page-encoded, the loader converts slot leaves to page leaves on the fly.
    monad_db_snapshot_loader *const loader = monad_db_snapshot_loader_create(
        block, dbname_paths, len, sq_thread_cpu, load_to_secondary);

    auto const do_mmap = [](std::filesystem::path const file) {
        using namespace monad;
        MONAD_ASSERT_PRINTF(
            std::filesystem::is_regular_file(file),
            "snapshot input file missing or not a regular file: %s",
            file.c_str());
        errno = 0;
        int const fd = open(file.c_str(), O_RDONLY);
        MONAD_ASSERT_PRINTF(
            fd != -1,
            "failed to open %s: %s",
            file.c_str(),
            std::strerror(errno));

        unsigned long const size = std::filesystem::file_size(file);
        void *data = nullptr;
        if (size) {
            data = mmap(nullptr, size, PROT_READ, MAP_SHARED, fd, 0);
            MONAD_ASSERT_PRINTF(
                data != MAP_FAILED,
                "failed to mmap %s: %s",
                file.c_str(),
                std::strerror(errno));
            // optimize for sequential accesses
            MONAD_ASSERT_PRINTF(
                madvise(data, size, MADV_SEQUENTIAL) == 0,
                "madvise failed for %s: %s",
                file.c_str(),
                std::strerror(errno));

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
            auto const calculated_hash = to_bytes(
                blake3({reinterpret_cast<unsigned char const *>(data), size}));
            MONAD_ASSERT_PRINTF(
                stored_hash == calculated_hash,
                "calculated checksum does not match stored checksum for file "
                "%s",
                file.c_str());
        }
        return std::make_tuple(
            fd, reinterpret_cast<unsigned char const *>(data), size);
    };

    for (auto const &dir : std::filesystem::directory_iterator{root}) {
        uint64_t const shard = std::stoull(dir.path().stem());
        auto const [eth_header_fd, eth_header, eth_header_len] =
            do_mmap(dir.path() / "eth_header");
        auto const [account_fd, account, account_len] =
            do_mmap(dir.path() / "account");
        auto const [storage_fd, storage, storage_len] =
            do_mmap(dir.path() / "storage");
        auto const [code_fd, code, code_len] = do_mmap(dir.path() / "code");
        monad_db_snapshot_loader_load(
            loader,
            shard,
            eth_header,
            eth_header_len,
            account,
            account_len,
            storage,
            storage_len,
            code,
            code_len);
        if (eth_header) {
            munmap((void *)eth_header, eth_header_len);
        }
        if (account) {
            munmap((void *)account, account_len);
        }
        if (storage) {
            munmap((void *)storage, storage_len);
        }
        if (code) {
            munmap((void *)code, code_len);
        }
        close(eth_header_fd);
        close(account_fd);
        close(storage_fd);
        close(code_fd);
    }

    monad_db_snapshot_loader_destroy(loader);
}
