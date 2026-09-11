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

#include <category/async/storage_pool.hpp>

#include <category/async/config.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/detail/start_lifetime_as_polyfill.hpp>
#include <category/core/hash.hpp>
#include <category/core/log.hpp>

#include <algorithm>
#include <atomic>
#include <cassert>
#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <limits>
#include <utility>
#include <variant>

#include <stdlib.h>

#include <asm-generic/ioctl.h>
#include <fcntl.h>
#include <linux/falloc.h>
#include <linux/limits.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <unistd.h>

MONAD_ASYNC_NAMESPACE_BEGIN

// DBs created before the num_cnv_chunks footer field existed store 0 there;
// such pools were always carved with this many conventional chunks.
static constexpr uint32_t legacy_default_num_cnv_chunks = 3;

std::filesystem::path storage_pool::device_t::current_path() const
{
    std::filesystem::path::string_type ret;
    ret.resize(32769);
    char *const out = ret.data();
    // Linux keeps a symlink at /proc/self/fd/n
    char in[64];
    snprintf(in, sizeof(in), "/proc/self/fd/%d", readwritefd_);
    ssize_t const len = ::readlink(in, out, 32768);
    MONAD_ASSERT_PRINTF(
        len != -1, "readlink failed due to %s", std::strerror(errno));
    ret.resize(static_cast<size_t>(len));
    // Linux prepends or appends a " (deleted)" when a fd is nameless
    if (ret.size() >= 10 &&
        ((ret.compare(0, 10, " (deleted)") == 0) ||
         (ret.compare(ret.size() - 10, 10, " (deleted)") == 0))) {
        ret.clear();
    }
    return ret;
}

size_t storage_pool::device_t::chunks() const
{
    MONAD_ASSERT(!is_zoned_device(), "zonefs support isn't implemented yet");
    return metadata_->chunks(size_of_file_);
}

size_t storage_pool::device_t::cnv_chunks() const
{
    MONAD_ASSERT(!is_zoned_device(), "zonefs support isn't implemented yet");
    return metadata_->num_cnv_chunks == 0 ? legacy_default_num_cnv_chunks
                                          : metadata_->num_cnv_chunks;
}

std::pair<file_offset_t, file_offset_t> storage_pool::device_t::capacity() const
{
    switch (type_) {
    case device_t::type_t_::file: {
        struct stat stat;
        MONAD_ASSERT_PRINTF(
            -1 != ::fstat(readwritefd_, &stat),
            "failed due to %s",
            std::strerror(errno));
        return {
            file_offset_t(stat.st_size), file_offset_t(stat.st_blocks) * 512};
    }
    case device_t::type_t_::block_device: {
        file_offset_t capacity;
        // Start with the pool metadata on the device
        file_offset_t used =
            round_up_align<CPU_PAGE_BITS>(metadata_->total_size(size_of_file_));
        // Add the capacity of the cnv chunk
        used += metadata_->chunk_capacity;
        MONAD_ASSERT_PRINTF(
            !ioctl(
                readwritefd_,
                _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/,
                &capacity),
            "failed due to %s",
            std::strerror(errno));
        auto const chunks = this->chunks();
        for (size_t n = 0; n < chunks; n++) {
            used += metadata_->chunk_bytes_used_at(size_of_file_, n)
                        .load(std::memory_order_acquire);
        }
        return {capacity, used};
    }
    case device_t::type_t_::zoned_device:
        MONAD_ABORT("zonefs support isn't implemented yet");
    default:
        MONAD_ABORT();
    }
}

/***************************************************************************/

std::pair<int, file_offset_t> storage_pool::chunk_t::write_fd(
    size_t const bytes_which_shall_be_written) noexcept
{
    if (device().is_file() || device().is_block_device()) {
        if (!append_only_) {
            return std::pair<int, file_offset_t>{
                device().readwritefd_, offset_};
        }
        auto const *const metadata = device().metadata_;
        MONAD_ASSERT(
            bytes_which_shall_be_written <=
            std::numeric_limits<uint32_t>::max());
        auto const cbu = metadata->chunk_bytes_used_at(
            device().size_of_file_, chunkid_within_device_);
        auto const size =
            (bytes_which_shall_be_written > 0)
                ? cbu.fetch_add(
                      static_cast<uint32_t>(bytes_which_shall_be_written),
                      std::memory_order_acq_rel)
                : cbu.load(std::memory_order_acquire);
        MONAD_ASSERT_PRINTF(
            size + bytes_which_shall_be_written <= metadata->chunk_capacity,
            "size %u bytes which shall be written %zu chunk capacity %u",
            size,
            bytes_which_shall_be_written,
            metadata->chunk_capacity);
        return std::pair<int, file_offset_t>{
            device().readwritefd_, offset_ + size};
    }
    MONAD_ABORT("zonefs support isn't implemented yet");
}

file_offset_t storage_pool::chunk_t::size() const
{
    if (device().is_file() || device().is_block_device()) {
        auto *const metadata = device().metadata_;
        if (!append_only_) {
            // Conventional chunks are always full
            return metadata->chunk_capacity;
        }
        return metadata
            ->chunk_bytes_used_at(
                device().size_of_file_, chunkid_within_device_)
            .load(std::memory_order_acquire);
    }
    MONAD_ABORT("zonefs support isn't implemented yet");
}

void storage_pool::chunk_t::destroy_contents()
{
    if (!try_trim_contents(0)) {
        MONAD_ABORT("zonefs support isn't implemented yet");
    }
}

uint32_t
storage_pool::chunk_t::clone_contents_into(chunk_t &other, uint32_t bytes)
{
    if (other.is_sequential_write() && other.size() != 0) {
        MONAD_ABORT(
            "Append only destinations must be empty before content clone");
    }
    bytes = std::min(uint32_t(size()), bytes);
    auto const rdfd = read_fd();
    auto const wrfd = other.write_fd(bytes);
    auto off_in = off64_t(rdfd.second);
    auto off_out = off64_t(wrfd.second);
    auto bytescopied =
        copy_file_range(rdfd.first, &off_in, wrfd.first, &off_out, bytes, 0);
    if (bytescopied == -1) {
        auto *const p = aligned_alloc(DISK_PAGE_SIZE, bytes);
        MONAD_ASSERT_PRINTF(
            p != nullptr, "failed due to %s", std::strerror(errno));
        auto const unp = make_scope_exit([&]() noexcept { ::free(p); });
        bytescopied =
            ::pread(rdfd.first, p, bytes, static_cast<off_t>(rdfd.second));
        MONAD_ASSERT_PRINTF(
            -1 != bytescopied, "failed due to %s", std::strerror(errno));
        MONAD_ASSERT_PRINTF(
            -1 != ::pwrite(
                      wrfd.first,
                      p,
                      static_cast<size_t>(bytescopied),
                      static_cast<off_t>(wrfd.second)),
            "failed due to %s",
            std::strerror(errno));
    }
    return uint32_t(bytescopied);
}

bool storage_pool::chunk_t::try_trim_contents(uint32_t bytes)
{
    bytes = std::min(uint32_t(size()), bytes);
    MONAD_ASSERT(capacity_ <= std::numeric_limits<off_t>::max());
    MONAD_ASSERT(offset_ <= std::numeric_limits<off_t>::max());
    if (device().is_file()) {
        MONAD_ASSERT_PRINTF(
            -1 != ::fallocate(
                      device().readwritefd_,
                      FALLOC_FL_KEEP_SIZE | FALLOC_FL_PUNCH_HOLE,
                      static_cast<off_t>(offset_ + bytes),
                      static_cast<off_t>(capacity_ - bytes)),
            "failed due to %s",
            std::strerror(errno));
        if (append_only_) {
            auto const *metadata = device().metadata_;
            metadata
                ->chunk_bytes_used_at(
                    device().size_of_file_, chunkid_within_device_)
                .store(bytes, std::memory_order_release);
        }
        return true;
    }
    if (device().is_block_device()) {
        // Round where our current append point is down to its nearest
        // DISK_PAGE_SIZE, aiming to TRIM all disk pages between that
        // and the end of our chunk in a single go
        uint64_t range[2] = {
            round_down_align<DISK_PAGE_BITS>(offset_ + bytes), 0};
        range[1] = offset_ + capacity_ - range[0];

        // TODO(niall): Should really read
        // /sys/block/nvmeXXX/queue/discard_granularity and
        // /sys/block/nvmeXXX/queue/discard_max_bytes and adjust accordingly,
        // however every NVMe SSD I'm aware of has 512 and 2Tb. If we ran on MMC
        // or legacy SATA SSDs this would be very different, but we never will.
        auto const remainder = offset_ + bytes - range[0];
        MONAD_ASSERT(remainder < DISK_PAGE_SIZE);
        if (remainder > 0) {
            auto *const buffer = reinterpret_cast<std::byte *>(
                aligned_alloc(DISK_PAGE_SIZE, DISK_PAGE_SIZE));
            auto const unbuffer =
                make_scope_exit([&]() noexcept { ::free(buffer); });
            // Copy any fragment of DISK_PAGE_SIZE about to get TRIMed to a
            // temporary buffer
            MONAD_ASSERT_PRINTF(
                -1 != ::pread(
                          device().readwritefd_,
                          buffer,
                          DISK_PAGE_SIZE,
                          static_cast<off_t>(range[0])),
                "failed due to %s",
                std::strerror(errno));
            // Overwrite the first DISK_PAGE_SIZE unit with all bits after
            // truncation point set to zero
            memset(buffer + remainder, 0, DISK_PAGE_SIZE - remainder);
            MONAD_ASSERT_PRINTF(
                -1 != ::pwrite(
                          device().readwritefd_,
                          buffer,
                          DISK_PAGE_SIZE,
                          static_cast<off_t>(range[0])),
                "failed due to %s",
                std::strerror(errno));
            // TRIM only the remaining DISK_PAGE_SIZE-aligned bytes
            range[0] += DISK_PAGE_SIZE;
            range[1] -= DISK_PAGE_SIZE;
        }
        if (range[1] > 0) {
            MONAD_ASSERT(range[0] >= offset_ && range[0] < offset_ + capacity_);
            MONAD_ASSERT(range[1] <= capacity_);
            MONAD_ASSERT((range[1] & (DISK_PAGE_SIZE - 1)) == 0);
            MONAD_ASSERT_PRINTF(
                !ioctl(
                    device().readwritefd_,
                    _IO(0x12, 119) /*BLKDISCARD*/,
                    &range),
                "failed due to %s",
                std::strerror(errno));
        }
        if (append_only_) {
            auto const *metadata = device().metadata_;
            metadata
                ->chunk_bytes_used_at(
                    device().size_of_file_, chunkid_within_device_)
                .store(bytes, std::memory_order_release);
        }
        return true;
    }
    /* For zonefs, the documentation is unclear if you can truncate
    a sequential zone to anything other than its maximum extent or
    zero. It seems reasonable it would allow any 512 byte granularity.
    Worth trying if we implement support for zonefs.
    */
    return false;
}

/***************************************************************************/

storage_pool::device_t storage_pool::make_device_(
    mode const op, device_t::type_t_ const type,
    std::filesystem::path const &path, int const fd,
    std::variant<uint64_t, device_t const *> dev_no_or_dev,
    creation_flags const flags)
{
    int readwritefd = fd;
    uint64_t const chunk_capacity = 1ULL << flags.chunk_capacity;
    auto unique_hash = fnv1a_hash<uint32_t>::begin();
    if (auto const *dev_no = std::get_if<0>(&dev_no_or_dev)) {
        fnv1a_hash<uint32_t>::add(unique_hash, uint32_t(type));
        fnv1a_hash<uint32_t>::add(unique_hash, uint32_t(*dev_no));
        fnv1a_hash<uint32_t>::add(unique_hash, uint32_t(*dev_no >> 32));
    }
    if (!path.empty()) {
        readwritefd = ::open(
            path.c_str(),
            ((flags.open_read_only || flags.open_read_only_allow_dirty)
                 ? O_RDONLY
                 : O_RDWR) |
                O_CLOEXEC);
        MONAD_ASSERT_PRINTF(
            readwritefd != -1, "open failed due to %s", std::strerror(errno));
    }
    struct stat stat;
    memset(&stat, 0, sizeof(stat));
    switch (type) {
    case device_t::type_t_::file:
        MONAD_ASSERT_PRINTF(
            -1 != ::fstat(readwritefd, &stat),
            "failed due to %s",
            std::strerror(errno));
        break;
    case device_t::type_t_::block_device:
        MONAD_ASSERT_PRINTF(
            !ioctl(
                readwritefd,
                _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/,
                &stat.st_size),
            "failed due to %s",
            std::strerror(errno));
        break;
    case device_t::type_t_::zoned_device:
        MONAD_ABORT("zonefs support isn't implemented yet");
    default:
        abort();
    }
    if (stat.st_size < CPU_PAGE_SIZE) {
        MONAD_ABORT_PRINTF(
            "Storage pool source %s must be at least 4Kb long to be used with "
            "storage pool",
            path.string().c_str());
    }
    fnv1a_hash<uint32_t>::add(unique_hash, uint32_t(stat.st_size));
    size_t total_size = 0;
    {
        auto *const buffer = reinterpret_cast<std::byte *>(
            aligned_alloc(DISK_PAGE_SIZE, DISK_PAGE_SIZE * 2));
        auto const unbuffer =
            make_scope_exit([&]() noexcept { ::free(buffer); });
        auto const offset = round_down_align<DISK_PAGE_BITS>(
            file_offset_t(stat.st_size) - sizeof(device_t::metadata_t));
        MONAD_ASSERT(offset <= std::numeric_limits<off_t>::max());
        MONAD_ASSERT(static_cast<size_t>(stat.st_size) > offset);
        auto const bytesread = ::pread(
            readwritefd,
            buffer,
            static_cast<size_t>(stat.st_size) - offset,
            static_cast<off_t>(offset));
        MONAD_ASSERT_PRINTF(
            bytesread != -1, "pread failed due to %s", std::strerror(errno));
        auto *const metadata_footer = start_lifetime_as<device_t::metadata_t>(
            buffer + bytesread - sizeof(device_t::metadata_t));
        if (memcmp(metadata_footer->magic, "MND0", 4) != 0 ||
            op == mode::truncate) {
            // Uninitialised
            if (op == mode::open_existing) {
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s has not been initialised "
                    "for use with storage pool",
                    path.string().c_str());
            }
            if (stat.st_size < (1LL << flags.chunk_capacity) + CPU_PAGE_SIZE) {
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s must be at least chunk_capacity + "
                    "4Kb long to be "
                    "initialised for use with storage pool",
                    path.string().c_str());
            }
            // Throw away all contents
            switch (type) {
            case device_t::type_t_::file:
                MONAD_ASSERT_PRINTF(
                    ::ftruncate(readwritefd, 0) != -1,
                    "failed due to %s",
                    std::strerror(errno));
                MONAD_ASSERT_PRINTF(
                    ::ftruncate(readwritefd, stat.st_size) != -1,
                    "failed due to %s",
                    std::strerror(errno));
                break;
            case device_t::type_t_::block_device: {
                uint64_t range[2] = {0, uint64_t(stat.st_size)};
                if (ioctl(readwritefd, _IO(0x12, 119) /*BLKDISCARD*/, &range)) {
                    MONAD_ABORT_PRINTF(
                        "ioctl failed due to %s", std::strerror(errno));
                }
                break;
            }
            case device_t::type_t_::zoned_device:
                MONAD_ABORT("zonefs support isn't implemented yet");
            default:
                abort();
            }
            memset(buffer, 0, DISK_PAGE_SIZE * 2);
            MONAD_ASSERT(
                chunk_capacity <= std::numeric_limits<uint32_t>::max());
            for (off_t offset2 = static_cast<off_t>(
                     offset - round_up_align<DISK_PAGE_BITS>(
                                  (monad::async::file_offset_t(stat.st_size) /
                                   chunk_capacity * sizeof(uint32_t))));
                 offset2 < static_cast<off_t>(offset);
                 offset2 += DISK_PAGE_SIZE) {
                MONAD_ASSERT_PRINTF(
                    ::pwrite(readwritefd, buffer, DISK_PAGE_SIZE, offset2) > 0,
                    "failed due to %s",
                    std::strerror(errno));
            }
            memcpy(metadata_footer->magic, "MND0", 4);
            metadata_footer->chunk_capacity =
                static_cast<uint32_t>(chunk_capacity);
            metadata_footer->num_cnv_chunks = flags.num_cnv_chunks;
            MONAD_ASSERT_PRINTF(
                ::pwrite(
                    readwritefd,
                    buffer,
                    static_cast<size_t>(bytesread),
                    static_cast<off_t>(offset)) > 0,
                "failed due to %s",
                std::strerror(errno));
        }
        total_size =
            metadata_footer->total_size(static_cast<size_t>(stat.st_size));
        uint32_t const stored_num_cnv_chunks =
            metadata_footer->num_cnv_chunks == 0
                ? legacy_default_num_cnv_chunks
                : metadata_footer->num_cnv_chunks;
        if (flags.num_cnv_chunks > stored_num_cnv_chunks) {
            LOG_WARNING(
                "Flag-specified num_cnv_chunks ({}) is greater than the value "
                "stored in metadata ({}). This setting will be ignored. "
                "Existing databases cannot be reconfigured to use more chunks, "
                "create a new database if you need a higher num_cnv_chunks.",
                flags.num_cnv_chunks,
                stored_num_cnv_chunks);
        }
    }
    size_t const offset = round_down_align<CPU_PAGE_BITS>(
        static_cast<size_t>(stat.st_size) - total_size);
    size_t const bytestomap = round_up_align<CPU_PAGE_BITS>(
        static_cast<size_t>(stat.st_size) - offset);
    void *const addr = ::mmap(
        nullptr,
        bytestomap,
        (flags.open_read_only && !flags.open_read_only_allow_dirty)
            ? (PROT_READ)
            : (PROT_READ | PROT_WRITE),
        flags.open_read_only_allow_dirty ? MAP_PRIVATE : MAP_SHARED,
        readwritefd,
        static_cast<off_t>(offset));
    MONAD_ASSERT_PRINTF(
        MAP_FAILED != addr, "mmap failed due to %s", std::strerror(errno));
    auto *const metadata = start_lifetime_as<device_t::metadata_t>(
        reinterpret_cast<std::byte *>(addr) + stat.st_size - offset -
        sizeof(device_t::metadata_t));
    MONAD_ASSERT(0 == memcmp(metadata->magic, "MND0", 4));
    if (auto const **const dev = std::get_if<1>(&dev_no_or_dev)) {
        unique_hash = (*dev)->unique_hash_;
    }
    return device_t(
        readwritefd,
        type,
        unique_hash,
        static_cast<size_t>(stat.st_size),
        metadata);
}

void storage_pool::adopt_device_(creation_flags const &flags)
{
    MONAD_ASSERT_PRINTF(
        device_.is_file() || device_.is_block_device(),
        "zonefs support isn't implemented yet");
    uint32_t const cnv_chunks_count =
        static_cast<uint32_t>(device_.cnv_chunks());
    auto const devicechunks = device_.chunks();
    MONAD_ASSERT_PRINTF(
        devicechunks >= cnv_chunks_count + 1,
        "Device %s has %zu chunks the minimum allowed is %u.",
        device_.current_path().c_str(),
        devicechunks,
        cnv_chunks_count + 1);
    MONAD_ASSERT(devicechunks <= std::numeric_limits<uint32_t>::max());
    uint32_t const seq_chunks_count =
        static_cast<uint32_t>(devicechunks) - cnv_chunks_count;

    auto hashshouldbe = fnv1a_hash<uint32_t>::begin();
    fnv1a_hash<uint32_t>::add(hashshouldbe, uint32_t(device_.unique_hash_));
    fnv1a_hash<uint32_t>::add(
        hashshouldbe, uint32_t(device_.unique_hash_ >> 32));
    fnv1a_hash<uint32_t>::add(
        hashshouldbe, static_cast<uint32_t>(devicechunks));
    fnv1a_hash<uint32_t>::add(hashshouldbe, device_.metadata_->chunk_capacity);
    if (device_.metadata_->config_hash == 0) {
        device_.metadata_->config_hash = uint32_t(hashshouldbe);
    }
    else if (device_.metadata_->config_hash != uint32_t(hashshouldbe)) {
        if (!flags.disable_mismatching_storage_pool_check) {
            MONAD_ABORT_PRINTF(
                "Storage pool source %s was initialised with a configuration "
                "different to this storage pool. Has it been resized since the "
                "pool was created?\n\nYou should use the monad-mpt tool to "
                "copy and move databases around, NOT by copying partition "
                "contents!",
                device_.current_path().c_str());
        }
        else {
            MONAD_ABORT_PRINTF(
                "Storage pool source %s was initialised with a configuration "
                "different to this storage pool. Has it been resized since the "
                "pool was created?\n\nYou should use the monad-mpt tool to "
                "copy and move databases around, NOT by copying partition "
                "contents!\n\nSince the monad-mpt tool was added, the flag "
                "disable_mismatching_storage_pool_check is no longer needed "
                "and has been disabled.",
                device_.current_path().c_str());
        }
    }

    // The first cnv_chunks_count chunks are conventional, the remainder
    // sequential.
    cnv_chunks_count_ = cnv_chunks_count;
    seq_chunks_count_ = seq_chunks_count;
}

storage_pool::device_t
storage_pool::reopen_device_read_only_(device_t const &src)
{
    creation_flags flags;
    flags.open_read_only = true;
    auto const path = src.current_path();
    int const fd = [&] {
        if (!path.empty()) {
            return ::open(path.c_str(), O_PATH | O_CLOEXEC);
        }
        char procpath[PATH_MAX];
        sprintf(procpath, "/proc/self/fd/%d", src.readwritefd_);
        return ::open(procpath, O_RDONLY | O_CLOEXEC);
    }();
    MONAD_ASSERT_PRINTF(
        fd != -1, "open failed due to %s", std::strerror(errno));
    auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    if (path.empty()) {
        unfd.release();
    }
    if (src.is_block_device()) {
        return make_device_(
            mode::open_existing,
            device_t::type_t_::block_device,
            path,
            fd,
            &src,
            flags);
    }
    if (src.is_file()) {
        return make_device_(
            mode::open_existing,
            device_t::type_t_::file,
            path,
            fd,
            &src,
            flags);
    }
    if (src.is_zoned_device()) {
        MONAD_ABORT("zonefs support isn't actually implemented yet");
    }
    MONAD_ABORT();
}

storage_pool::device_t storage_pool::open_device_(
    std::filesystem::path const &source, mode const op,
    creation_flags const flags)
{
    int const fd = ::open(source.c_str(), O_PATH | O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1, "open failed due to %s", std::strerror(errno));
    auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    struct statfs statfs;
    MONAD_ASSERT_PRINTF(
        -1 != ::fstatfs(fd, &statfs), "failed due to %s", std::strerror(errno));
    MONAD_ASSERT(
        statfs.f_type != 0x5a4f4653 /*ZONEFS_MAGIC*/,
        "zonefs support isn't actually implemented yet");
    struct stat stat;
    MONAD_ASSERT_PRINTF(
        -1 != ::fstat(fd, &stat), "failed due to %s", std::strerror(errno));
    if ((stat.st_mode & S_IFMT) == S_IFBLK) {
        return make_device_(
            op,
            device_t::type_t_::block_device,
            source.c_str(),
            fd,
            0ULL,
            flags);
    }
    if ((stat.st_mode & S_IFMT) == S_IFREG) {
        return make_device_(
            op,
            device_t::type_t_::file,
            source.c_str(),
            fd,
            stat.st_ino,
            flags);
    }
    MONAD_ABORT_PRINTF(
        "Storage pool source %s has unknown file entry type = %u",
        source.string().c_str(),
        stat.st_mode & S_IFMT);
}

storage_pool::device_t storage_pool::make_anonymous_device_(
    off_t const len, creation_flags const flags)
{
    int const fd = make_temporary_inode();
    auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    MONAD_ASSERT_PRINTF(
        -1 != ::ftruncate(fd, len), "failed due to %s", std::strerror(errno));
    auto device = make_device_(
        mode::truncate, device_t::type_t_::file, {}, fd, uint64_t(0), flags);
    unfd.release();
    return device;
}

storage_pool::storage_pool(
    storage_pool const *const src, clone_as_read_only_tag_)
    : is_read_only_(true)
    , is_read_only_allow_dirty_(false)
    , is_migration_allowed_(false)
    , is_newly_truncated_(false)
    , device_(reopen_device_read_only_(src->device_))
{
    creation_flags flags;
    flags.open_read_only = true;
    adopt_device_(flags);
}

storage_pool::storage_pool(
    std::filesystem::path const &source, mode const mode,
    creation_flags const flags)
    : is_read_only_(flags.open_read_only || flags.open_read_only_allow_dirty)
    , is_read_only_allow_dirty_(flags.open_read_only_allow_dirty)
    , is_migration_allowed_(flags.allow_migration)
    , is_newly_truncated_(mode == mode::truncate)
    , device_(open_device_(source, mode, flags))
{
    adopt_device_(flags);
}

storage_pool::storage_pool(use_anonymous_inode_tag, creation_flags const flags)
    : storage_pool::storage_pool(
          use_anonymous_sized_inode_tag{},
          1ULL * 1024 * 1024 * 1024 * 1024 + 24576, flags)
{
}

storage_pool::storage_pool(
    use_anonymous_sized_inode_tag, off_t const len, creation_flags const flags)
    : is_read_only_(flags.open_read_only || flags.open_read_only_allow_dirty)
    , is_read_only_allow_dirty_(flags.open_read_only_allow_dirty)
    , is_migration_allowed_(flags.allow_migration)
    , is_newly_truncated_(false)
    , device_(make_anonymous_device_(len, flags))
{
    adopt_device_(flags);
}

storage_pool::~storage_pool()
{
    if (device_.metadata_ != nullptr) {
        auto const total_size =
            device_.metadata_->total_size(device_.size_of_file_);
        ::munmap(
            reinterpret_cast<void *>(round_down_align<CPU_PAGE_BITS>(
                (uintptr_t)device_.metadata_ + sizeof(device_t::metadata_t) -
                total_size)),
            total_size);
    }
    if (device_.readwritefd_ != -1) {
        (void)::fsync(device_.readwritefd_);
        (void)::close(device_.readwritefd_);
    }
}

storage_pool::chunk_t
storage_pool::chunk(chunk_type const which, uint32_t const id)
{
    MONAD_ASSERT_PRINTF(
        id < chunks(which),
        "Requested %s chunk %u but the pool has %zu",
        which == cnv ? "conventional" : "sequential",
        id,
        chunks(which));
    MONAD_ASSERT_PRINTF(!device_.is_zoned_device(), "zonefs isn't implemented");
    // Conventional chunks come first on the device, sequential ones after
    // them.
    uint32_t const id_within_device =
        which == cnv ? id : cnv_chunks_count_ + id;
    auto const capacity = device_.metadata_->chunk_capacity;
    return chunk_t{
        device_,
        file_offset_t(id_within_device) * capacity,
        capacity,
        id_within_device,
        id,
        which == seq};
}

storage_pool storage_pool::clone_as_read_only() const
{
    return storage_pool(this, clone_as_read_only_tag_{});
}

MONAD_ASYNC_NAMESPACE_END
