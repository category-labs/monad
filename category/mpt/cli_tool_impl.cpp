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

#include <CLI/CLI.hpp>

#include "cli_tool_impl.hpp"

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/detail/start_lifetime_as_polyfill.hpp>
#include <category/async/io.hpp>
#include <category/async/storage_pool.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/detail/db_metadata.hpp>
#include <category/mpt/detail/kbhit.hpp>
#include <category/mpt/trie.hpp>

#include <quill/Quill.h>

#include <evmc/hex.hpp>

#include <algorithm>
#include <atomic>
#include <bit>
#include <cctype>
#include <cerrno>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <exception>
#include <filesystem>
#include <future>
#include <iomanip>
#include <iostream>
#include <iterator>
#include <optional>
#include <span>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <thread>
#include <utility>
#include <vector>

#include <archive.h>
#include <archive_entry.h>
#include <bits/time.h>
#include <bits/types/struct_sched_param.h>
#include <fcntl.h>
#include <pthread.h>
#include <sched.h>
#include <sys/mman.h>
#include <sys/statfs.h>
#include <time.h>
#include <unistd.h>
#include <zstd.h>

std::string print_bytes(MONAD_ASYNC_NAMESPACE::file_offset_t bytes_)
{
    auto bytes = double(bytes_);
    std::stringstream s;
    s << std::fixed << std::setprecision(2);
    if (bytes >= 0.9 * 1024 * 1024 * 1024 * 1024 * 1024) {
        bytes /= 1024.0 * 1024 * 1024 * 1024 * 1024;
        s << bytes << " Pb";
        return std::move(s).str();
    }
    if (bytes >= 0.9 * 1024 * 1024 * 1024 * 1024) {
        bytes /= 1024.0 * 1024 * 1024 * 1024;
        s << bytes << " Tb";
        return std::move(s).str();
    }
    if (bytes >= 0.9 * 1024 * 1024 * 1024) {
        bytes /= 1024.0 * 1024 * 1024;
        s << bytes << " Gb";
        return std::move(s).str();
    }
    if (bytes >= 0.9 * 1024 * 1024) {
        bytes /= 1024.0 * 1024;
        s << bytes << " Mb";
        return std::move(s).str();
    }
    if (bytes >= 0.9 * 1024) {
        bytes /= 1024.0;
        s << bytes << " Kb";
        return std::move(s).str();
    }
    s << bytes << " bytes";
    return std::move(s).str();
}

static size_t const true_hardware_concurrency = [] {
    auto v = std::thread::hardware_concurrency();
    int const fd = ::open("/sys/devices/system/cpu/smt/active", O_RDONLY);
    if (fd != -1) {
        char buffer = 0;
        if (::read(fd, &buffer, 1) == 1) {
            if (buffer == '1') {
                v /= 2;
            }
        }
        ::close(fd);
    }
    return v;
}();
static size_t const total_physical_memory_bytes = [] {
    auto v = sysconf(_SC_PHYS_PAGES);
    if (v == -1) {
        throw std::system_error(errno, std::system_category());
    }
    return size_t(v) * size_t(getpagesize());
}();

struct chunk_info_restore_t
{
    monad::async::storage_pool::chunk_type const type;
    uint32_t const chunk_id;
    monad::mpt::detail::db_metadata::chunk_info_t const metadata;
    std::span<std::byte const> const compressed;

    monad::async::storage_pool::chunk_t *chunk_ptr;
    std::vector<std::byte> nonchunkstorage;
    std::future<size_t> decompression_thread;
    bool const is_uncompressed;
    bool use_faster_memory_mode{false};
    bool done{false};

    chunk_info_restore_t(
        monad::async::storage_pool::chunk_type type_, uint32_t chunk_id_,
        monad::mpt::detail::db_metadata::chunk_info_t metadata_,
        std::span<std::byte const> compressed_, bool is_uncompressed_)
        : type(type_)
        , chunk_id(chunk_id_)
        , metadata(metadata_)
        , compressed(compressed_)
        , is_uncompressed(is_uncompressed_)
    {
    }

    chunk_info_restore_t(chunk_info_restore_t const &) = delete;

    chunk_info_restore_t(chunk_info_restore_t &&) = default;

    chunk_info_restore_t &operator=(chunk_info_restore_t const &) = delete;

    chunk_info_restore_t &operator=(chunk_info_restore_t &&o) noexcept
    {
        if (this != &o) {
            this->~chunk_info_restore_t();
            new (this) chunk_info_restore_t(std::move(o));
        }
        return *this;
    }

    ~chunk_info_restore_t()
    {
        reset();
    }

    void reset() {}

    // Runs in a separate kernel thread
    size_t run()
    {
        if (!is_uncompressed) {
            std::span<std::byte> decompressed;
            auto undecompressed = monad::make_scope_exit([&]() noexcept {
                if (decompressed.data() != nullptr) {
                    ::munmap(decompressed.data(), decompressed.size());
                }
            });
            if (nonchunkstorage.empty()) {
                auto const decompressed_len = ZSTD_getFrameContentSize(
                    compressed.data(), compressed.size());
                if (use_faster_memory_mode) {
                    decompressed = {
                        (std::byte *)::mmap(
                            nullptr,
                            decompressed_len,
                            PROT_READ | PROT_WRITE,
                            MAP_PRIVATE | MAP_ANONYMOUS,
                            -1,
                            0),
                        size_t(decompressed_len)};
                    if (decompressed.data() == MAP_FAILED) {
                        throw std::system_error(errno, std::system_category());
                    }
                }
                else {
                    // We don't have enough physical RAM, so use
                    // files as temporary backing storage
                    int const fd = monad::async::make_temporary_inode();
                    if (fd == -1) {
                        throw std::system_error(errno, std::system_category());
                    }
                    if (-1 == ftruncate(fd, off_t(decompressed_len))) {
                        throw std::system_error(errno, std::system_category());
                    }
                    decompressed = {
                        (std::byte *)::mmap(
                            nullptr,
                            decompressed_len,
                            PROT_READ | PROT_WRITE,
                            MAP_SHARED,
                            fd,
                            0),
                        size_t(decompressed_len)};
                    if (decompressed.data() == MAP_FAILED) {
                        throw std::system_error(errno, std::system_category());
                    }
                    ::close(fd);
                }
            }
            else {
                undecompressed.release();
                decompressed = {nonchunkstorage};
            }

            auto const written = ZSTD_decompress(
                decompressed.data(),
                decompressed.size(),
                compressed.data(),
                compressed.size());
            if (ZSTD_isError(written)) {
                throw std::runtime_error("ZSTD compression failed");
            }
            if (nonchunkstorage.empty()) {
                auto [wfd, offset] = chunk_ptr->write_fd(written);
                if (::pwrite(
                        wfd,
                        decompressed.data(),
                        decompressed.size(),
                        off_t(offset)) < 0) {
                    throw std::system_error(errno, std::system_category());
                }
            }
            return written;
        }
        else {
            if (nonchunkstorage.empty()) {
                auto [wfd, offset] = chunk_ptr->write_fd(compressed.size());
                if (::pwrite(
                        wfd,
                        compressed.data(),
                        compressed.size(),
                        off_t(offset)) < 0) {
                    throw std::system_error(errno, std::system_category());
                }
            }
            else {
                memcpy(
                    nonchunkstorage.data(),
                    compressed.data(),
                    compressed.size());
            }
            return compressed.size();
        }
    }
};

struct chunk_info_archive_t
{
    monad::async::storage_pool::chunk_t const *chunk_ptr;
    la_int64_t const metadata;

    void *compressed_storage{nullptr};
    size_t compressed_storage_size{0};
    void const *uncompressed_storage{nullptr};
    std::span<std::byte> compressed;
    std::span<std::byte const> uncompressed;
    std::future<void> compression_thread;

    chunk_info_archive_t(
        monad::async::storage_pool::chunk_t *chunk_ptr_, la_int64_t metadata_)
        : chunk_ptr(std::move(chunk_ptr_))
        , metadata(metadata_)
    {
    }

    chunk_info_archive_t(chunk_info_archive_t &&o) noexcept
        : chunk_ptr(std::move(o.chunk_ptr))
        , metadata(o.metadata)
        , compressed_storage(o.compressed_storage)
        , compressed_storage_size(o.compressed_storage_size)
        , uncompressed_storage(o.uncompressed_storage)
        , compressed(o.compressed)
        , uncompressed(o.uncompressed)
        , compression_thread(std::move(o.compression_thread))
    {
        o.compressed_storage = nullptr;
        o.uncompressed_storage = nullptr;
    }

    ~chunk_info_archive_t()
    {
        reset();
    }

    void reset()
    {
        if (compressed_storage != nullptr) {
            ::munmap(compressed_storage, compressed_storage_size);
            compressed_storage = nullptr;
        }
        if (uncompressed_storage != nullptr) {
            ::munmap((void *)uncompressed_storage, uncompressed.size());
            uncompressed_storage = nullptr;
        }
    }

    // Runs in a separate kernel thread
    void run(int const compression_level)
    {
        int const fd = monad::async::make_temporary_inode();
        if (fd == -1) {
            throw std::system_error(errno, std::system_category());
        }
        compressed_storage_size = (compression_level != 0)
                                      ? ZSTD_compressBound(uncompressed.size())
                                      : uncompressed.size();
        if (-1 == ftruncate(fd, off_t(compressed_storage_size))) {
            throw std::system_error(errno, std::system_category());
        }
        compressed_storage = ::mmap(
            nullptr,
            compressed_storage_size,
            PROT_READ | PROT_WRITE,
            MAP_SHARED,
            fd,
            0);
        ::close(fd);
        if (compressed_storage == MAP_FAILED) {
            throw std::system_error(errno, std::system_category());
        }
        compressed = {(std::byte *)compressed_storage, compressed_storage_size};
        if (compression_level != 0) {
            /* Compression level benchmarks:

            1 -  972 Mb/sec, max 6 concurrency (I think some pool
            stalls occurred). Wrote 146.25 for 179.56.

            2 - 1086 Mb/sec, max 8 concurrency. Wrote 150.91 for
            179.56 input.

            3 - 1079 Mb/sec, max 11 concurrency. Wrote 147.61 for
            179.56 input.

            4 - 986 Mb/sec, max 13 concurrency. Wrote 146.25 for
            179.56 input.

            */
            auto const written = ZSTD_compress(
                compressed.data(),
                compressed.size(),
                uncompressed.data(),
                uncompressed.size(),
                compression_level);
            if (ZSTD_isError(written)) {
                throw std::runtime_error("ZSTD compression failed");
            }
            compressed = compressed.subspan(0, written);
        }
        else {
            memcpy(compressed.data(), uncompressed.data(), uncompressed.size());
        }
    }
};

struct impl_t
{
    std::ostream &cout;
    std::ostream &cerr;
    MONAD_ASYNC_NAMESPACE::storage_pool::creation_flags flags;
    uint8_t chunk_capacity = flags.chunk_capacity;
    uint32_t root_offsets_chunk_count = 16;
    bool allow_dirty = false;
    bool no_prompt = false;
    bool create_database = false;
    bool truncate_database = false;
    bool create_empty_database = false;
    std::optional<uint64_t> rewind_database_to;
    std::optional<uint64_t> reset_history_length;
    bool create_chunk_increasing = false;
    bool debug_printing = false;
    std::filesystem::path archive_database;
    std::filesystem::path restore_database;
    std::vector<std::filesystem::path> storage_paths;
    int compression_level = 3;

    std::optional<MONAD_ASYNC_NAMESPACE::storage_pool> pool;

    std::vector<chunk_info_archive_t> fast, slow;
    MONAD_ASYNC_NAMESPACE::file_offset_t total_used = 0;

public:
    impl_t(std::ostream &cout_, std::ostream &cerr_)
        : cout(cout_)
        , cerr(cerr_)
    {
    }

    void cli_ask_question(char const *msg)
    {
        if (!no_prompt) {
            auto answer = tty_ask_question(msg);
            cout << std::endl;
            if (tolower(answer) != 'y') {
                cout << "Aborting." << std::endl;
                exit(0);
            }
        }
    };

    template <class T = void>
    MONAD_ASYNC_NAMESPACE::file_offset_t print_list_info(
        MONAD_MPT_NAMESPACE::UpdateAuxImpl &aux,
        MONAD_MPT_NAMESPACE::detail::db_metadata::chunk_info_t const
            *const item_,
        char const *name, T *list = nullptr)
    {
        if (item_ == nullptr) {
            cout << "     " << name << ": 0 chunks" << std::endl;
            return 0;
        }
        MONAD_ASYNC_NAMESPACE::file_offset_t total_capacity = 0, total_used = 0;
        uint32_t count = 0;
        auto const *item = item_;
        do {
            auto chunkid = item->index(aux.db_metadata());
            count++;
            auto &chunk = pool->chunk(pool->seq, chunkid);
            MONAD_DEBUG_ASSERT(chunk.zone_id().second == chunkid);
            if constexpr (!std::is_void_v<T>) {
                if (list != nullptr) {
                    la_int64_t const metadata =
                        std::bit_cast<la_int64_t>(*item);
                    list->emplace_back(std::addressof(chunk), metadata);
                }
            }
            total_capacity += chunk.capacity();
            total_used += chunk.size();
            item = item->next(aux.db_metadata());
        }
        while (item != nullptr);
        cout << "     " << name << ": " << count << " chunks with capacity "
             << print_bytes(total_capacity) << " used "
             << print_bytes(total_used) << std::endl;
        if (debug_printing) {
            std::cerr << "        ";
            item = item_;
            do {
                auto chunkid = item->index(aux.db_metadata());
                std::cerr << " " << chunkid << " ("
                          << uint32_t(item->insertion_count()) << ")";
                item = item->next(aux.db_metadata());
            }
            while (item != nullptr);
            std::cerr << std::endl;
        }
        return total_used;
    }

    void print_db_history_summary(MONAD_MPT_NAMESPACE::UpdateAuxImpl &aux)
    {
        cout << "MPT database has "
             << (1 + aux.db_history_max_version() -
                 aux.db_history_min_valid_version())
             << " history, earliest is " << aux.db_history_min_valid_version()
             << " latest is " << aux.db_history_max_version()
             << ".\n     It has been configured to retain no more than "
             << aux.version_history_length() << ".\n     Latest proposed is ("
             << aux.get_latest_proposed_version() << ", "
             << evmc::hex(monad::byte_string_view(
                    aux.get_latest_proposed_block_id().bytes,
                    sizeof(monad::bytes32_t)))
             << ").\n     Latest voted is (" << aux.get_latest_voted_version()
             << ", "
             << evmc::hex(monad::byte_string_view(
                    aux.get_latest_voted_block_id().bytes,
                    sizeof(monad::bytes32_t)))
             << ").\n     Latest finalized is "
             << aux.get_latest_finalized_version() << ", latest verified is "
             << aux.get_latest_verified_version() << ", auto expire version is "
             << aux.get_auto_expire_version_metadata() << "\n";
    }

    void do_restore_database()
    {
        auto const begin = std::chrono::steady_clock::now();
        int fd = ::open(restore_database.c_str(), O_RDONLY | O_CLOEXEC);
        if (fd == -1) {
            throw std::system_error(errno, std::system_category());
        }
        auto unfd = monad::make_scope_exit([&]() noexcept { ::close(fd); });

        struct archive_shared_t
        {
            size_t map_size{0};
            std::byte const *map_addr{nullptr};

            ~archive_shared_t()
            {
                ::munmap((void *)map_addr, map_size);
            }
        } archive_shared;

        {
            struct stat stat;
            if (-1 == ::fstat(fd, &stat)) {
                throw std::system_error(errno, std::system_category());
            }
            archive_shared.map_size = size_t(stat.st_size);
        }
        archive_shared.map_addr = (std::byte const *)::mmap(
            nullptr, archive_shared.map_size, PROT_READ, MAP_SHARED, fd, 0);
        if (archive_shared.map_addr == MAP_FAILED) {
            throw std::system_error(errno, std::system_category());
        }
        unfd.reset();

        auto *in = archive_read_new();
        auto unin =
            monad::make_scope_exit([&]() noexcept { archive_read_free(in); });
        if (ARCHIVE_OK != archive_read_support_format_tar(in)) {
            std::stringstream ss;
            ss << "libarchive failed due to " << archive_error_string(in);
            throw std::runtime_error(ss.str());
        }
        if (ARCHIVE_OK != archive_read_support_filter_all(in)) {
            std::stringstream ss;
            ss << "libarchive failed due to " << archive_error_string(in);
            throw std::runtime_error(ss.str());
        }

        if (ARCHIVE_OK !=
            archive_read_open_memory(
                in, archive_shared.map_addr, archive_shared.map_size)) {
            std::stringstream ss;
            ss << "libarchive failed due to " << archive_error_string(in);
            throw std::runtime_error(ss.str());
        }

        std::vector<chunk_info_restore_t> todecompress;
        uint32_t max_chunk_id[2] = {0, 0};
        for (archive_entry *entry = nullptr;
             archive_read_next_header(in, &entry) == ARCHIVE_OK;) {
            std::filesystem::path const pathname(archive_entry_pathname(entry));
            monad::async::storage_pool::chunk_type type;
            std::string_view const pathname_sv(pathname.native());
            auto const type_sv = pathname_sv.substr(0, 4);
            if (type_sv == "cnv/") {
                type = monad::async::storage_pool::cnv;
            }
            else if (type_sv == "seq/") {
                type = monad::async::storage_pool::seq;
            }
            else {
                continue;
            }
            bool const is_uncompressed =
                (pathname_sv.find(".zst") == pathname_sv.npos);
            uint32_t const chunk_id = uint32_t(atol(pathname.stem().c_str()));
            monad::mpt::detail::db_metadata::chunk_info_t metadata;
            memset(&metadata, 0, sizeof(metadata));
            archive_entry_xattr_reset(entry);
            char const *xattr_name = nullptr;
            void const *xattr_value = nullptr;
            size_t xattr_value_len = 0;
            for (;;) {
                archive_entry_xattr_next(
                    entry, &xattr_name, &xattr_value, &xattr_value_len);
                if (xattr_name == nullptr) {
                    break;
                }
                if (0 == strcmp(xattr_name, "monad.triedb.metadata")) {
                    memcpy(&metadata, xattr_value, sizeof(metadata));
                }
            }
            if (type == monad::async::storage_pool::seq) {
                if (!metadata.in_fast_list && !metadata.in_slow_list) {
                    std::stringstream ss;
                    ss << "Sequential type chunk in archive has neither "
                          "fast list nor slow list bits set. Are you sure "
                          "this archive was generated by monad-mpt?";
                    throw std::runtime_error(ss.str());
                }
            }
            void const *buffer = nullptr;
            size_t len = 0;
            off_t offset = 0;
            if (archive_read_data_block(in, &buffer, &len, &offset) !=
                ARCHIVE_OK) {
                std::stringstream ss;
                ss << "libarchive failed due to " << archive_error_string(in);
                throw std::runtime_error(ss.str());
            }
            if (chunk_id > max_chunk_id[type]) {
                max_chunk_id[type] = chunk_id;
            }
            todecompress.emplace_back(
                type,
                chunk_id,
                metadata,
                std::span<std::byte const>{(std::byte const *)buffer, len},
                is_uncompressed);
        }
        cout << "The archived database " << restore_database << " contains "
             << todecompress.size() << " chunks." << std::endl;

        // Does the destination pool have enough chunks?
        if (max_chunk_id[monad::async::storage_pool::cnv] >=
            pool->chunks(monad::async::storage_pool::cnv)) {
            std::stringstream ss;
            ss << "DB archive " << restore_database << " uses cnv chunks up to "
               << max_chunk_id[monad::async::storage_pool::cnv]
               << ", but the destination pool's cnv chunk count is "
               << pool->chunks(monad::async::storage_pool::cnv)
               << ". You will need to configure a destination pool with "
                  "more cnv chunks.";
            throw std::runtime_error(ss.str());
        }
        if (max_chunk_id[monad::async::storage_pool::seq] >=
            pool->chunks(monad::async::storage_pool::seq)) {
            std::stringstream ss;
            ss << "DB archive " << restore_database << " uses seq chunks up to "
               << max_chunk_id[monad::async::storage_pool::seq]
               << ", but the destination pool's seq chunk count is "
               << pool->chunks(monad::async::storage_pool::seq)
               << ". You will need to configure a destination pool with "
                  "more seq chunks.";
            throw std::runtime_error(ss.str());
        }

        // Does the destination pool use a chunk size larger or equal to the
        // archive's chunks?
        size_t max_decompressed_len = 0;
        for (auto &i : todecompress) {
            auto const decompressed_len =
                i.is_uncompressed
                    ? i.compressed.size()
                    : ZSTD_getFrameContentSize(
                          i.compressed.data(), i.compressed.size());
            if (decompressed_len == ZSTD_CONTENTSIZE_UNKNOWN ||
                decompressed_len == ZSTD_CONTENTSIZE_ERROR) {
                throw std::runtime_error("zstd failed");
            }
            if (i.type == monad::async::storage_pool::cnv && i.chunk_id == 0) {
                // Decompress the triedb metadata into a temporary region
                // instead of a pool chunk
                i.nonchunkstorage.resize(size_t(decompressed_len));
            }
            else {
                i.chunk_ptr = std::addressof(pool->chunk(i.type, i.chunk_id));
                if (decompressed_len > i.chunk_ptr->capacity()) {
                    std::stringstream ss;
                    ss << "DB archive " << restore_database << " chunk id "
                       << i.chunk_id << " uses "
                       << print_bytes(decompressed_len)
                       << " after decompression however the destination "
                          "pool's "
                          "chunk capacity is "
                       << print_bytes(i.chunk_ptr->capacity())
                       << ". You will need to configure a destination pool "
                          "with larger chunks.";
                    throw std::runtime_error(ss.str());
                }
                if (decompressed_len > max_decompressed_len) {
                    max_decompressed_len = decompressed_len;
                }
            }
        }
        if (max_decompressed_len * true_hardware_concurrency <=
            total_physical_memory_bytes / 2) {
            cout << "\nAs maximum RAM consumption used by "
                    "decompression ("
                 << print_bytes(
                        max_decompressed_len * true_hardware_concurrency)
                 << ") is less than half the physical memory of the "
                    "machine ("
                 << print_bytes(total_physical_memory_bytes)
                 << "), enabling fast decompression mode." << std::endl;
            for (auto &i : todecompress) {
                i.use_faster_memory_mode = true;
            }
        }
        else {
            cout << "\nAs maximum RAM consumption used by "
                    "decompression ("
                 << print_bytes(
                        max_decompressed_len * true_hardware_concurrency)
                 << ") is more than than half the physical memory of the "
                    "machine ("
                 << print_bytes(total_physical_memory_bytes)
                 << "), using slow decompression mode." << std::endl;
        }

        // Set up an empty triedb into the pool
        std::vector<uint32_t> chunks;
        chunks.reserve(1024);
        {
            monad::io::Ring ring(monad::io::RingConfig{1});
            monad::io::Buffers rwbuf =
                monad::io::make_buffers_for_mixed_read_write(
                    ring,
                    2,
                    2,
                    MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
                    MONAD_ASYNC_NAMESPACE::AsyncIO::
                        MONAD_IO_BUFFERS_WRITE_SIZE);
            auto io = MONAD_ASYNC_NAMESPACE::AsyncIO{*pool, rwbuf};
            MONAD_MPT_NAMESPACE::UpdateAux<> aux(io);
            for (;;) {
                auto const *item = aux.db_metadata()->fast_list_begin();
                if (item == nullptr) {
                    break;
                }
                auto chunkid = item->index(aux.db_metadata());
                MONAD_ASSERT(chunkid != UINT32_MAX);
                aux.remove(chunkid);
                chunks.push_back(chunkid);
            }
            for (;;) {
                auto const *item = aux.db_metadata()->slow_list_begin();
                if (item == nullptr) {
                    break;
                }
                auto chunkid = item->index(aux.db_metadata());
                MONAD_ASSERT(chunkid != UINT32_MAX);
                aux.remove(chunkid);
                chunks.push_back(chunkid);
            }
            for (;;) {
                auto const *item = aux.db_metadata()->free_list_begin();
                if (item == nullptr) {
                    break;
                }
                auto chunkid = item->index(aux.db_metadata());
                MONAD_ASSERT(chunkid != UINT32_MAX);
                aux.remove(chunkid);
                chunks.push_back(chunkid);
            }
        }

        // Do the decompression into the pool
        cout << std::endl;
        monad::async::file_offset_t total_bytes_decompressed = 0;
        for (;;) {
            size_t done = 0;
            size_t max_concurrency = 0;
            for (auto &i : todecompress) {
                if (i.done) {
                    done++;
                }
                else {
                    if (max_concurrency < true_hardware_concurrency) {
                        if (!i.decompression_thread.valid()) {
                            i.decompression_thread =
                                std::async(std::launch::async, [i = &i] {
                                    return i->run();
                                });
                        }
                        if (i.decompression_thread.wait_for(
                                std::chrono::seconds(0)) !=
                            std::future_status::timeout) {
                            total_bytes_decompressed +=
                                i.decompression_thread.get();
                            i.done = true;
                            i.reset();
                        }
                        else {
                            max_concurrency++;
                        }
                    }
                }
            }
            cout << "\rProgress: " << done << "/" << todecompress.size() << "  "
                 << (100 * done / todecompress.size()) << "%        "
                 << std::flush;
            if (done == todecompress.size()) {
                break;
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(1));
        }
        cout << std::endl;

        // Fix up triedb metadata to match archived
        monad::mpt::detail::unsigned_20 fast_list_base_insertion_count(
            UINT32_MAX);
        monad::mpt::detail::unsigned_20 slow_list_base_insertion_count(
            UINT32_MAX);
        uint32_t fast_list_begin_index{UINT32_MAX};
        uint32_t fast_list_end_index{UINT32_MAX};
        uint32_t slow_list_begin_index{UINT32_MAX};
        uint32_t slow_list_end_index{UINT32_MAX};
        for (auto &i : todecompress) {
            if (i.type == monad::async::storage_pool::cnv) {
                if (i.chunk_id == 0) {
                    auto const *old_metadata =
                        (monad::mpt::detail::db_metadata const *)
                            i.nonchunkstorage.data();
                    if (memcmp(
                            old_metadata->magic,
                            monad::mpt::detail::db_metadata::MAGIC,
                            monad::mpt::detail::db_metadata::
                                MAGIC_STRING_LEN)) {
                        std::stringstream ss;
                        ss << "DB archive was generated with version "
                           << old_metadata->magic
                           << ". The current code base is on version "
                           << monad::mpt::detail::db_metadata::MAGIC
                           << ". Please regenerate archive with the new DB "
                              "version.";
                        throw std::runtime_error(ss.str());
                    }
                    auto &cnv_chunk =
                        pool->chunk(monad::async::storage_pool::cnv, 0);
                    auto [wfd, offset] = cnv_chunk.write_fd(0);
                    auto *new_metadata_map = ::mmap(
                        nullptr,
                        cnv_chunk.capacity(),
                        PROT_READ | PROT_WRITE,
                        MAP_SHARED,
                        wfd,
                        off_t(offset));
                    if (new_metadata_map == MAP_FAILED) {
                        throw std::system_error(errno, std::system_category());
                    }
                    auto un_new_metadata_map =
                        monad::make_scope_exit([&]() noexcept {
                            ::munmap(new_metadata_map, cnv_chunk.capacity());
                        });
                    monad::mpt::detail::db_metadata *db_metadata[2] = {
                        (monad::mpt::detail::db_metadata *)new_metadata_map,
                        (monad::mpt::detail::db_metadata
                             *)((std::byte *)new_metadata_map +
                                cnv_chunk.capacity() / 2)};
                    auto do_ = [&](auto &&f) {
                        f(db_metadata[0]);
                        f(db_metadata[1]);
                    };
                    do_([&](monad::mpt::detail::db_metadata *metadata) {
                        MONAD_ASSERT(
                            0 == memcmp(
                                     metadata->magic,
                                     monad::mpt::detail::db_metadata::MAGIC,
                                     monad::mpt::detail::db_metadata::
                                         MAGIC_STRING_LEN));
                    });
                    do_([&](monad::mpt::detail::db_metadata *metadata) {
                        metadata->db_offsets.store(old_metadata->db_offsets);
                        metadata->root_offsets.next_version_ =
                            old_metadata->root_offsets.next_version_;
                        metadata->root_offsets.version_lower_bound_ =
                            old_metadata->root_offsets.version_lower_bound_;
                        memcpy(
                            &metadata->root_offsets.storage_,
                            &old_metadata->root_offsets.storage_,
                            sizeof(metadata->root_offsets.storage_));
                        metadata->history_length = old_metadata->history_length;
                        metadata->latest_finalized_version =
                            old_metadata->latest_finalized_version;
                        metadata->latest_verified_version =
                            old_metadata->latest_verified_version;
                        metadata->latest_voted_version =
                            old_metadata->latest_voted_version;
                        metadata->latest_voted_block_id =
                            old_metadata->latest_voted_block_id;
                        metadata->auto_expire_version =
                            old_metadata->auto_expire_version;
                    });
                    fast_list_base_insertion_count =
                        old_metadata->fast_list_begin()->insertion_count();
                    slow_list_base_insertion_count =
                        old_metadata->slow_list_begin()->insertion_count();
                    MONAD_ASSERT(old_metadata->fast_list.begin != UINT32_MAX);
                    MONAD_ASSERT(old_metadata->slow_list.begin != UINT32_MAX);
                    fast_list_begin_index = old_metadata->fast_list.begin;
                    slow_list_begin_index = old_metadata->slow_list.begin;
                    if (auto const max_seq_chunk = std::max(
                            fast_list_begin_index, slow_list_begin_index);
                        max_seq_chunk >=
                        pool->chunks(monad::async::storage_pool::seq)) {
                        std::stringstream ss;
                        ss << "DB archive " << restore_database
                           << " uses seq chunks up to " << max_seq_chunk
                           << " in db metadata, but the destination pool's seq "
                              "chunk count is "
                           << pool->chunks(monad::async::storage_pool::seq)
                           << ". You will need to configure a destination pool "
                              "with more seq chunks.";
                        throw std::runtime_error(ss.str());
                    }
                    fast_list_end_index = old_metadata->fast_list.end;
                    slow_list_end_index = old_metadata->slow_list.end;
                    break;
                }
            }
        }

        // Sort chunks into correct order, fast list by insertion count,
        // then slow list by insertion count, with all cnv chunks to the end
        std::sort(
            todecompress.begin(),
            todecompress.end(),
            [fast_list_base_insertion_count, slow_list_base_insertion_count](
                chunk_info_restore_t const &a, chunk_info_restore_t const &b) {
                if (a.type > b.type) {
                    return true;
                }
                if (a.type == b.type) {
                    if (a.metadata.in_fast_list && !b.metadata.in_fast_list) {
                        return true;
                    }
                    if (a.metadata.in_fast_list == b.metadata.in_fast_list ||
                        a.metadata.in_slow_list == b.metadata.in_slow_list) {
                        if (a.metadata.in_fast_list) {
                            return (a.metadata.insertion_count() -
                                    fast_list_base_insertion_count) <
                                   (b.metadata.insertion_count() -
                                    fast_list_base_insertion_count);
                        }
                        else {
                            return (a.metadata.insertion_count() -
                                    slow_list_base_insertion_count) <
                                   (b.metadata.insertion_count() -
                                    slow_list_base_insertion_count);
                        }
                    }
                }
                return false;
            });

        if (debug_printing) {
            std::cerr << "Fast list:";
            auto it = todecompress.begin();
            for (; it != todecompress.end() && it->metadata.in_fast_list;
                 ++it) {
                std::cerr << " " << it->chunk_id;
            }
            std::cerr << "\nSlow list:";
            for (; it != todecompress.end() &&
                   it->type == monad::async::storage_pool::seq;
                 ++it) {
                std::cerr << " " << it->chunk_id;
            }
            std::cerr << std::endl;
        }

        // Use UpdateAux to adjust the fast and slow lists
        monad::io::Ring ring(monad::io::RingConfig{1});
        monad::io::Buffers rwbuf = monad::io::make_buffers_for_read_only(
            ring,
            2,
            MONAD_ASYNC_NAMESPACE::AsyncIO::MONAD_IO_BUFFERS_READ_SIZE);
        auto io = MONAD_ASYNC_NAMESPACE::AsyncIO{*pool, rwbuf};
        MONAD_MPT_NAMESPACE::UpdateAux<> aux(io);
        size_t slow_chunks_inserted = 0;
        size_t fast_chunks_inserted = 0;
        auto override_insertion_count =
            [](monad::mpt::detail::db_metadata *db,
               monad::mpt::UpdateAuxImpl::chunk_list type,
               monad::mpt::detail::unsigned_20 initial_insertion_count) {
                MONAD_ASSERT(
                    type != monad::mpt::UpdateAuxImpl::chunk_list::free);
                auto g = db->hold_dirty();
                auto *i =
                    const_cast<monad::mpt::detail::db_metadata::chunk_info_t *>(
                        type == monad::mpt::UpdateAuxImpl::chunk_list::fast
                            ? db->fast_list_begin()
                            : db->slow_list_begin());
                i->insertion_count0_ =
                    uint32_t(initial_insertion_count) & 0x3ff;
                i->insertion_count1_ =
                    uint32_t(initial_insertion_count >> 10) & 0x3ff;
            };
        for (auto &i : todecompress) {
            if (i.type == monad::async::storage_pool::seq) {
                if (i.metadata.in_fast_list) {
                    aux.append(
                        monad::mpt::UpdateAuxImpl::chunk_list::fast,
                        i.chunk_id);
                    if (0 == fast_chunks_inserted++) {
                        aux.modify_metadata(
                            override_insertion_count,
                            monad::mpt::UpdateAuxImpl::chunk_list::fast,
                            fast_list_base_insertion_count);
                    }
                }
                else if (i.metadata.in_slow_list) {
                    aux.append(
                        monad::mpt::UpdateAuxImpl::chunk_list::slow,
                        i.chunk_id);
                    if (0 == slow_chunks_inserted++) {
                        aux.modify_metadata(
                            override_insertion_count,
                            monad::mpt::UpdateAuxImpl::chunk_list::slow,
                            slow_list_base_insertion_count);
                    }
                }
                if (i.metadata.in_fast_list || i.metadata.in_slow_list) {
                    auto it =
                        std::find(chunks.begin(), chunks.end(), i.chunk_id);
                    MONAD_ASSERT(it != chunks.end());
                    *it = UINT32_MAX;
                }
            }
        }
        MONAD_ASSERT(
            slow_chunks_inserted + fast_chunks_inserted +
                max_chunk_id[monad::async::storage_pool::cnv] ==
            todecompress.size() - 1);
        if (fast_chunks_inserted == 0) {
            aux.append(
                monad::mpt::UpdateAuxImpl::chunk_list::fast,
                fast_list_begin_index);
            auto it =
                std::find(chunks.begin(), chunks.end(), fast_list_begin_index);
            MONAD_ASSERT(it != chunks.end());
            *it = UINT32_MAX;
            // override the first insertion count
            aux.modify_metadata(
                override_insertion_count,
                monad::mpt::UpdateAuxImpl::chunk_list::fast,
                fast_list_base_insertion_count);
        }
        MONAD_ASSERT(
            aux.db_metadata()->fast_list.begin == fast_list_begin_index);
        MONAD_ASSERT(aux.db_metadata()->fast_list.end == fast_list_end_index);

        if (slow_chunks_inserted == 0) {
            aux.append(
                monad::mpt::UpdateAuxImpl::chunk_list::slow,
                slow_list_begin_index);
            auto it =
                std::find(chunks.begin(), chunks.end(), slow_list_begin_index);
            MONAD_ASSERT(it != chunks.end());
            *it = UINT32_MAX;
            // override the first insertion count
            aux.modify_metadata(
                override_insertion_count,
                monad::mpt::UpdateAuxImpl::chunk_list::slow,
                slow_list_base_insertion_count);
        }
        MONAD_ASSERT(
            aux.db_metadata()->slow_list.begin == slow_list_begin_index);
        MONAD_ASSERT(aux.db_metadata()->slow_list.end == slow_list_end_index);

        for (unsigned int &chunk : chunks) {
            if (chunk != UINT32_MAX) {
                aux.append(monad::mpt::UpdateAuxImpl::chunk_list::free, chunk);
            }
        }

        auto const end = std::chrono::steady_clock::now();
        double const secs =
            double(std::chrono::duration_cast<std::chrono::microseconds>(
                       end - begin)
                       .count()) /
            1000000.0;
        cout << "\nDatabase has been restored from " << restore_database << " "
             << print_bytes(total_bytes_decompressed) << " long in " << secs
             << " seconds which is "
             << (double(total_bytes_decompressed) / 1024.0 / 1024.0 / secs)
             << " Mb/sec." << std::endl;
    }

    void do_archive_database()
    {
        auto const begin = std::chrono::steady_clock::now();
        int fd = ::open(
            archive_database.c_str(),
            O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC,
            0660);
        if (fd == -1) {
            throw std::system_error(errno, std::system_category());
        }
        auto unfd1 = monad::make_scope_fail(
            [&]() noexcept { ::unlink(archive_database.c_str()); });
        auto unfd2 = monad::make_scope_exit([&]() noexcept { ::close(fd); });

        {
            struct statfs statfs;
            if (-1 == ::fstatfs(fd, &statfs)) {
                throw std::system_error(errno, std::system_category());
            }
            if (total_used / monad::async::file_offset_t(statfs.f_bsize) >
                monad::async::file_offset_t(statfs.f_bavail)) {
                std::stringstream ss;
                ss << "WARNING: Destination filesystem for archive "
                   << archive_database << " has "
                   << print_bytes(
                          monad::async::file_offset_t(statfs.f_bavail) *
                          monad::async::file_offset_t(statfs.f_bsize))
                   << " available however the archived file may "
                      "consume "
                   << print_bytes(total_used)
                   << ". Are you sure you wish to proceed?\n";
                cli_ask_question(ss.str().c_str());
            }

            auto const total_used2 =
                std::thread::hardware_concurrency() /
                2 /* deliberately not
                     true_hardware_concurrency */
                * pool->chunk(monad::async::storage_pool::seq, 0).capacity();
            int const tempfd = monad::async::make_temporary_inode();
            if (tempfd == -1) {
                throw std::system_error(errno, std::system_category());
            }
            if (-1 == ::fstatfs(tempfd, &statfs)) {
                throw std::system_error(errno, std::system_category());
            }
            ::close(tempfd);
            if (total_used2 / monad::async::file_offset_t(statfs.f_bsize) >
                monad::async::file_offset_t(statfs.f_bavail)) {
                std::stringstream ss;
                ss << "WARNING: Temporary files filesystem "
                   << monad::async::working_temporary_directory() << " has "
                   << print_bytes(
                          monad::async::file_offset_t(statfs.f_bavail) *
                          monad::async::file_offset_t(statfs.f_bsize))
                   << " available however temporary files may "
                      "consume "
                   << print_bytes(total_used2)
                   << ". Are you sure you wish to proceed?\n";
                cli_ask_question(ss.str().c_str());
            }
        }
        {
            /* Set main thread priority to maximum possible so writing
             the archive has higher priority than compressing the
             blocks.
             */
            std::async(std::launch::async, [] {}).get();
            struct sched_param param;
            param.sched_priority = 20;
            if (pthread_setschedparam(pthread_self(), SCHED_FIFO, &param) !=
                0) {
                auto const *msg = strerror(errno);
                cerr << "WARNING: pthread_setschedparam failed with " << msg
                     << std::endl;
            }
        }
        {
            struct archive *out = archive_write_new();
            if (out == nullptr) {
                throw std::runtime_error("libarchive failed");
            }
            auto unout = monad::make_scope_exit([&]() noexcept {
                archive_write_close(out);
                archive_write_free(out);
            });
            if (ARCHIVE_OK != archive_write_set_format_pax_restricted(out)) {
                throw std::runtime_error("libarchive failed");
            }
            if (ARCHIVE_OK != archive_write_open_fd(out, fd)) {
                throw std::runtime_error("libarchive failed");
            }

            uint32_t additional_cnv_chunks_to_archive = 0;
            auto map_chunk_into_memory = [this,
                                          &additional_cnv_chunks_to_archive](
                                             chunk_info_archive_t &i) {
                auto [fd2, offset] = i.chunk_ptr->read_fd();
                i.uncompressed_storage = ::mmap(
                    nullptr,
                    i.chunk_ptr->size(),
                    PROT_READ,
                    MAP_SHARED,
                    fd2,
                    off_t(offset));
                if (i.uncompressed_storage == MAP_FAILED) {
                    throw std::system_error(errno, std::system_category());
                }
                i.uncompressed = {
                    (std::byte const *)i.uncompressed_storage,
                    i.chunk_ptr->size()};
                if (i.chunk_ptr->zone_id() == std::pair{pool->cnv, 0u}) {
                    // The first conventional chunk is where
                    // triedb metadata is stored. It has two
                    // copies with the backup copy stored half
                    // way through the chunk size. We don't need
                    // the second copy, so eliminate it
                    auto const db_metadata_size =
                        sizeof(monad::mpt::detail::db_metadata) +
                        pool->chunks(monad::async::storage_pool::seq) *
                            sizeof(
                                monad::mpt::detail::db_metadata::chunk_info_t);
                    i.uncompressed =
                        i.uncompressed.subspan(0, db_metadata_size);
                    auto const *m = monad::start_lifetime_as<
                        monad::mpt::detail::db_metadata>(i.uncompressed.data());
                    additional_cnv_chunks_to_archive =
                        m->root_offsets.storage_.cnv_chunks_len;
                }
                i.compression_thread =
                    std::async(std::launch::async, [i = &i, this] {
                        i->run(compression_level);
                    });
            };

            std::vector<chunk_info_archive_t *> tocompress;
            tocompress.reserve(
                pool->chunks(pool->cnv) + fast.size() + slow.size());
            std::vector<chunk_info_archive_t> cnv_infos;
            cnv_infos.reserve(pool->chunks(pool->cnv));
            for (uint32_t n = 0; n <= additional_cnv_chunks_to_archive; n++) {
                cnv_infos.emplace_back(
                    std::addressof(pool->chunk(pool->cnv, n)), -1);
                tocompress.push_back(&cnv_infos.back());
                if (n == 0) {
                    // Need to determine additional_cnv_chunks_to_archive
                    map_chunk_into_memory(cnv_infos.back());
                }
            }
            if (debug_printing) {
                std::cerr << "Fast list:";
            }
            for (auto &i : fast) {
                if (i.chunk_ptr->size() > 0) {
                    tocompress.push_back(&i);
                    MONAD_ASSERT(
                        i.chunk_ptr->zone_id().second <
                        pool->chunks(pool->seq));
                    if (debug_printing) {
                        std::cerr << " " << i.chunk_ptr->zone_id().second;
                    }
                }
            }
            if (debug_printing) {
                std::cerr << "\nSlow list:";
            }
            for (auto &i : slow) {
                if (i.chunk_ptr->size() > 0) {
                    tocompress.push_back(&i);
                    MONAD_ASSERT(
                        i.chunk_ptr->zone_id().second <
                        pool->chunks(pool->seq));
                    if (debug_printing) {
                        std::cerr << " " << i.chunk_ptr->zone_id().second;
                    }
                }
            }
            if (debug_printing) {
                std::cerr << std::endl;
            }
            cout << std::endl;
            for (auto it = tocompress.begin(); it != tocompress.end();) {
                size_t max_concurrency = 0;
                for (auto it2 = it;
                     it2 != tocompress.end() &&
                     max_concurrency < std::thread::hardware_concurrency() /
                                           2 /* deliberately not
                                                true_hardware_concurrency */
                     ;
                     ++it2, max_concurrency++) {
                    chunk_info_archive_t &i = **it2;
                    if (i.uncompressed_storage == nullptr) {
                        map_chunk_into_memory(i);
                    }
                    else if (
                        max_concurrency == 0 &&
                        i.compression_thread.wait_for(std::chrono::milliseconds(
                            10)) != std::future_status::timeout) {
                        i.compression_thread.get();
                        {
                            auto const dist =
                                std::distance(tocompress.begin(), it);
                            cout << "\rProgress: " << dist << "/"
                                 << tocompress.size() << "  "
                                 << (100 * dist / ssize_t(tocompress.size()))
                                 << "%        " << std::flush;
                        }
                        ++it;
                        struct archive_entry *entry = archive_entry_new();
                        if (entry == nullptr) {
                            throw std::runtime_error("libarchive failed");
                        }
                        auto unentry = monad::make_scope_exit(
                            [&]() noexcept { archive_entry_free(entry); });
                        std::string leafname;
                        auto const [chunktype, chunkid] =
                            i.chunk_ptr->zone_id();
                        if (chunktype == pool->cnv) {
                            leafname.append("cnv/");
                        }
                        else if (chunktype == pool->seq) {
                            leafname.append("seq/");
                        }
                        else {
                            MONAD_ASSERT(false);
                        }
                        leafname.append(std::to_string(chunkid));
                        if (compression_level != 0) {

                            leafname.append(".zst");
                        }
                        archive_entry_set_pathname(entry, leafname.c_str());
                        archive_entry_set_size(
                            entry, la_int64_t(i.compressed.size()));
                        archive_entry_set_filetype(entry, AE_IFREG);
                        archive_entry_set_perm(entry, 0644);
                        archive_entry_xattr_add_entry(
                            entry,
                            "monad.triedb.metadata",
                            &i.metadata,
                            sizeof(i.metadata));
                        struct timespec ts;
                        clock_gettime(CLOCK_REALTIME, &ts);
                        archive_entry_set_mtime(entry, ts.tv_sec, ts.tv_nsec);
                        if (ARCHIVE_OK != archive_write_header(out, entry)) {
                            std::stringstream ss;
                            ss << "libarchive failed due to "
                               << archive_error_string(out);
                            throw std::runtime_error(ss.str());
                        }
                        if (-1 == archive_write_data(
                                      out,
                                      i.compressed.data(),
                                      i.compressed.size())) {
                            std::stringstream ss;
                            ss << "libarchive failed due to "
                               << archive_error_string(out);
                            throw std::runtime_error(ss.str());
                        }
                        i.reset();
                    }
                }
            }
        }
        cout << std::endl;
        auto const end = std::chrono::steady_clock::now();
        double const secs =
            double(std::chrono::duration_cast<std::chrono::microseconds>(
                       end - begin)
                       .count()) /
            1000000.0;
        struct stat stat;
        if (-1 == ::fstat(fd, &stat)) {
            throw std::system_error(errno, std::system_category());
        }
        cout << "\nDatabase has been archived to " << archive_database << " "
             << print_bytes(monad::async::file_offset_t(stat.st_size))
             << " long in " << secs << " seconds which is "
             << (double(total_used) / 1024.0 / 1024.0 / secs) << " Mb/sec."
             << std::endl;
    }
};

int main_impl(
    std::ostream &cout, std::ostream &cerr, std::span<std::string_view> args)
{
    CLI::App cli("Tool for managing MPT databases", "monad-mpt");
    cli.footer(R"(Suitable sources of block storage:

1. Raw partitions on a storage device.
2. The storage device itself.
3. A file on a filing system (use 'truncate -s 1T sparsefile' to create and
set it to the desired size beforehand).

The storage source order must be identical to database creation, as must be
the source type, size and device id, otherwise the database cannot be
opened.
)");
    try {
        impl_t impl(cout, cerr);
        {
            auto *cli_ops_group = cli.add_option_group(
                "Mutating operations, if none of these are "
                "specified the storage is opened read-only");
            cli_ops_group->require_option(0, 1);
            cli.add_option(
                   "--storage",
                   impl.storage_paths,
                   "one or more sources of block storage (must be at least "
                   "<chunk_capacity> + 4Kb long).")
                ->required();
            cli.add_flag(
                "--allow-dirty",
                impl.allow_dirty,
                "allow the database to be opened even if its dirty flag is "
                "set. An "
                "attempt will be made to reconcile the two copies of metadata "
                "before proceeding.");
            cli.add_flag(
                "--yes",
                impl.no_prompt,
                "do not prompt before doing dangerous things.");
            cli_ops_group->add_flag(
                "--create",
                impl.create_database,
                "create a new database if needed, otherwise opens existing.");
            cli_ops_group->add_flag(
                "--truncate",
                impl.truncate_database,
                "truncates an existing database to empty, efficiently "
                "discarding "
                "all existing storage.");
            cli_ops_group->add_flag(
                "--create-empty",
                impl.create_empty_database,
                "create a new database if needed, otherwise truncate "
                "existing.");
            cli_ops_group->add_option(
                "--reset-history-length",
                impl.reset_history_length,
                "reset database history length to fixed length");
            cli_ops_group->add_option(
                "--rewind-to",
                impl.rewind_database_to,
                "rewind database to an earlier point in its history.");
            cli.add_option(
                "--archive",
                impl.archive_database,
                "archive an existing database to a compressed, portable file "
                "which "
                "can be later restored with this tool (implies "
                "--allow-dirty).");
            cli.add_option(
                "--restore",
                impl.restore_database,
                "destroy any existing database, replacing it with the archived "
                "database (implies --truncate).");
            cli.add_option(
                "--chunk-capacity",
                impl.chunk_capacity,
                "set chunk capacity during database creation (default is 28, "
                "1<<28 "
                "= 256Mb, max is 31).");
            cli.add_option(
                   "--root-offsets-chunk-count",
                   impl.root_offsets_chunk_count,
                   "Number of chunks to allocate for storing root offsets. "
                   "Must be a positive number that is a power of 2. Default is "
                   "16. Each chunk holds approx 16.5M history entries.")
                ->check([](std::string const &s) {
                    auto const v = std::stoll(s);
                    if (v <= 0) {
                        return "Value must be positive";
                    }
                    if ((v & (v - 1)) != 0) {
                        return "Value must be a power of 2";
                    }
                    return "";
                });
            cli.add_flag(
                "--chunk-increasing",
                impl.create_chunk_increasing,
                "if creating a new database, order the chunks sequentially "
                "increasing instead of randomly mixed.");
            cli.add_option(
                "--compression-level",
                impl.compression_level,
                "zstd compression to use during archival (default is 3, 0 "
                "disables, negative values are ultra fast, positive values "
                "past about 10 get real slow).");
            cli.add_flag(
                "--debug",
                impl.debug_printing,
                "print additional information useful for debugging issues.");
            {
                // Weirdly CLI11 wants reversed args for its vector consuming
                // overload
                std::vector<std::string> rargs(args.rbegin(), --args.rend());
                cli.parse(std::move(rargs));
            }

            quill::start(true);

            auto mode =
                MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing;
            impl.flags.chunk_capacity = impl.chunk_capacity & 31;
            if (impl.create_chunk_increasing) {
                impl.flags.interleave_chunks_evenly = true;
            }
            impl.flags.open_read_only = true;
            impl.flags.open_read_only_allow_dirty =
                impl.allow_dirty || !impl.archive_database.empty();
            impl.flags.num_cnv_chunks =
                impl.root_offsets_chunk_count +
                monad::mpt::UpdateAuxImpl::cnv_chunks_for_db_metadata;
            if (!impl.restore_database.empty()) {
                if (!impl.archive_database.empty()) {
                    impl.cli_ask_question(
                        "WARNING: Combining --restore with --archive will "
                        "first restore and then archive. Are you sure?\n");
                }
                impl.truncate_database = true;
            }
            if (impl.create_empty_database) {
                mode = MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate;
                impl.flags.open_read_only = false;
                impl.flags.open_read_only_allow_dirty = false;
                std::stringstream ss;
                ss << "WARNING: --create-empty will destroy all "
                      "existing data on";
                for (auto &i : impl.storage_paths) {
                    ss << " " << i;
                }
                ss << ". Are you sure?\n";
                impl.cli_ask_question(ss.str().c_str());
            }
            else if (impl.create_database) {
                mode =
                    MONAD_ASYNC_NAMESPACE::storage_pool::mode::create_if_needed;
                impl.flags.open_read_only = false;
                impl.flags.open_read_only_allow_dirty = false;
            }
            else if (impl.truncate_database) {
                mode = MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate;
                impl.flags.open_read_only = false;
                impl.flags.open_read_only_allow_dirty = false;
                std::stringstream ss;
                ss << "WARNING: --truncate will destroy all "
                      "existing data on";
                for (auto &i : impl.storage_paths) {
                    ss << " " << i;
                }
                ss << ". Are you sure?\n";
                impl.cli_ask_question(ss.str().c_str());
            }
            else if (impl.rewind_database_to || impl.reset_history_length) {
                impl.flags.open_read_only = false;
                impl.flags.open_read_only_allow_dirty = false;
            }
            if (mode == MONAD_ASYNC_NAMESPACE::storage_pool::mode::truncate) {
                MONAD_ASYNC_NAMESPACE::storage_pool const pool{
                    {impl.storage_paths}, mode, impl.flags};
                (void)pool;
                mode = MONAD_ASYNC_NAMESPACE::storage_pool::mode::open_existing;
            }
            impl.pool.emplace(std::span{impl.storage_paths}, mode, impl.flags);
        }

        if (!impl.restore_database.empty()) {
            impl.do_restore_database();
        }

        monad::io::Ring ring(monad::io::RingConfig{1});

        auto wr_ring(
            (impl.rewind_database_to || impl.reset_history_length)
                ? std::optional<monad::io::Ring>(monad::io::RingConfig{4})
                : std::nullopt);
        monad::io::Buffers rwbuf =
            (impl.rewind_database_to || impl.reset_history_length)
                ? monad::io::make_buffers_for_segregated_read_write(
                      ring,
                      *wr_ring,
                      2,
                      4,
                      MONAD_ASYNC_NAMESPACE::AsyncIO::
                          MONAD_IO_BUFFERS_READ_SIZE,
                      MONAD_ASYNC_NAMESPACE::AsyncIO::
                          MONAD_IO_BUFFERS_WRITE_SIZE)
                : monad::io::make_buffers_for_read_only(
                      ring,
                      2,
                      MONAD_ASYNC_NAMESPACE::AsyncIO::
                          MONAD_IO_BUFFERS_READ_SIZE);
        auto io = MONAD_ASYNC_NAMESPACE::AsyncIO{*impl.pool, rwbuf};
        MONAD_MPT_NAMESPACE::UpdateAux<> aux(io);

        {
            cout << R"(MPT database on storages:
          Capacity           Used      %  Path)";
            auto const default_width = int(cout.width());
            auto const default_prec = int(cout.precision());
            std::fixed(cout);
            for (auto const &device : impl.pool->devices()) {
                auto cap = device.capacity();
                cout << "\n   " << std::setw(15) << print_bytes(cap.first)
                     << std::setw(15) << print_bytes(cap.second) << std::setw(6)
                     << std::setprecision(2)
                     << (100.0 * double(cap.second) / double(cap.first))
                     << "%  " << device.current_path();
            }
            std::defaultfloat(cout);
            cout << std::setw(default_width) << std::setprecision(default_prec)
                 << std::endl;

            cout << "MPT database internal lists:\n";
            impl.total_used += impl.print_list_info(
                aux, aux.db_metadata()->fast_list_begin(), "Fast", &impl.fast);
            impl.total_used += impl.print_list_info(
                aux, aux.db_metadata()->slow_list_begin(), "Slow", &impl.slow);
            impl.print_list_info(
                aux, aux.db_metadata()->free_list_begin(), "Free");
            impl.print_db_history_summary(aux);

            if (impl.reset_history_length) {
                // set to fixed history length, database will prune any outdated
                // versions outside of new history length window
                cout << "\nResetting history length from "
                     << aux.version_history_length() << " to "
                     << impl.reset_history_length.value() << "... \n";
                if (impl.reset_history_length.value() <
                    aux.version_history_length()) {
                    std::stringstream ss;
                    ss << "WARNING: --reset-history-length can potentially "
                          "prune "
                          "historical versions and only keep the recent "
                       << impl.reset_history_length.value()
                       << " versions. Are you sure?\n";
                    impl.cli_ask_question(ss.str().c_str());
                }
                aux.unset_io();
                aux.set_io(io, impl.reset_history_length);
                cout << "Success! Done resetting history to "
                     << impl.reset_history_length.value() << ".\n";
                impl.print_db_history_summary(aux);
                return 0;
            }
            if (impl.rewind_database_to) {
                if (*impl.rewind_database_to <
                    aux.db_history_min_valid_version()) {
                    cout << "\nWARNING: Cannot rewind database to before "
                         << aux.db_history_min_valid_version()
                         << ", ignoring request.\n";
                }
                else if (
                    *impl.rewind_database_to >= aux.db_history_max_version()) {
                    cout << "\nWARNING: Cannot rewind database to after or "
                            "equal "
                         << aux.db_history_max_version()
                         << ", ignoring request.\n";
                }
                else {
                    std::stringstream ss;
                    ss << "\nWARNING: --rewind-to will destroy history "
                       << (*impl.rewind_database_to + 1) << " - "
                       << aux.db_history_max_version() << ". Are you sure?\n";
                    impl.cli_ask_question(ss.str().c_str());
                    aux.rewind_to_version(*impl.rewind_database_to);
                    cout << "\nSuccess! Now:\n";
                    impl.print_list_info(
                        aux, aux.db_metadata()->fast_list_begin(), "Fast");
                    impl.print_list_info(
                        aux, aux.db_metadata()->slow_list_begin(), "Slow");
                    impl.print_list_info(
                        aux, aux.db_metadata()->free_list_begin(), "Free");
                    return 0;
                }
            }
            if (!impl.archive_database.empty()) {
                impl.do_archive_database();
            }
        }
    }

    catch (const CLI::CallForHelp &e) {
        cout << cli.help() << std::flush;
    }

    catch (const CLI::RequiredError &e) {
        cerr << "FATAL: " << e.what() << "\n\n";
        cerr << cli.help() << std::flush;
        return 1;
    }

    catch (std::exception const &e) {
        cerr << "FATAL: " << e.what() << std::endl;
        return 1;
    }

    return 0;
}
