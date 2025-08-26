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

#include <category/async/detail/scope_polyfill.hpp>
#include <category/core/assert.h>
#include <category/core/hash.hpp>

#include <category/async/config.hpp>
#include <category/async/detail/start_lifetime_as_polyfill.hpp>
#include <category/async/util.hpp>

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
#include <format>
#include <iostream>
#include <limits>
#include <memory>
#include <mutex>
#include <span>
#include <sstream>
#include <stdexcept>
#include <stdlib.h>
#include <system_error>
#include <utility>
#include <variant>
#include <vector>

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

std::filesystem::path storage_pool::device::current_path() const
{
    std::filesystem::path::string_type ret;
    ret.resize(32769);
    auto *out = const_cast<char *>(ret.data());
    // Linux keeps a symlink at /proc/self/fd/n
    char in[64];
    snprintf(in, sizeof(in), "/proc/self/fd/%d", readwritefd_);
    ssize_t const len = ::readlink(in, out, 32768);
    MONAD_ASSERT_PRINTF(
        len != -1, "readlink failed due to %s", strerror(errno));
    ret.resize(static_cast<size_t>(len));
    // Linux prepends or appends a " (deleted)" when a fd is nameless
    if (ret.size() >= 10 &&
        ((ret.compare(0, 10, " (deleted)") == 0) ||
         (ret.compare(ret.size() - 10, 10, " (deleted)") == 0))) {
        ret.clear();
    }
    return ret;
}

size_t storage_pool::device::chunks() const
{
    MONAD_ASSERT(!is_zoned_device(), "zonefs support isn't implemented yet");
    return metadata_->chunks(size_of_file_);
}

std::pair<file_offset_t, file_offset_t> storage_pool::device::capacity() const
{
    switch (type_) {
    case device::type_t_::file: {
        struct stat stat;
        MONAD_ASSERT_PRINTF(
            -1 != ::fstat(readwritefd_, &stat),
            "failed due to %s",
            strerror(errno));
        return {
            file_offset_t(stat.st_size), file_offset_t(stat.st_blocks) * 512};
    }
    case device::type_t_::block_device: {
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
            strerror(errno));
        auto const chunks = this->chunks();
        auto const useds = metadata_->chunk_bytes_used(size_of_file_);
        for (size_t n = 0; n < chunks; n++) {
            used += useds[n].load(std::memory_order_acquire);
        }
        return {capacity, used};
    }
    case device::type_t_::zoned_device:
        MONAD_ABORT("zonefs support isn't implemented yet");
    default:
        MONAD_ABORT();
    }
}

/***************************************************************************/

storage_pool::chunk::chunk::~chunk()
{
    if (owns_readfd_ || owns_writefd_) {
        auto fd = read_fd_;
        if (owns_readfd_ && read_fd_ != -1) {
            (void)::close(read_fd_);
            read_fd_ = -1;
        }
        if (owns_writefd_ && write_fd_ != -1) {
            if (write_fd_ != fd) {
                (void)::close(write_fd_);
            }
            write_fd_ = -1;
        }
    }
}

std::pair<int, file_offset_t>
storage_pool::chunk::write_fd(size_t bytes_which_shall_be_written) noexcept
{
    if (device().is_file() || device().is_block_device()) {
        if (!append_only_) {
            return std::pair<int, file_offset_t>{write_fd_, offset_};
        }
        auto const *metadata = device().metadata_;
        auto chunk_bytes_used =
            metadata->chunk_bytes_used(device().size_of_file_);
        MONAD_DEBUG_ASSERT(
            bytes_which_shall_be_written <=
            std::numeric_limits<uint32_t>::max());
        auto size =
            (bytes_which_shall_be_written > 0)
                ? chunk_bytes_used[chunkid_within_device_].fetch_add(
                      static_cast<uint32_t>(bytes_which_shall_be_written),
                      std::memory_order_acq_rel)
                : chunk_bytes_used[chunkid_within_device_].load(
                      std::memory_order_acquire);
        MONAD_ASSERT_PRINTF(
            size + bytes_which_shall_be_written <= metadata->chunk_capacity,
            "size %u bytes which shall be written %zu chunk capacity %u",
            size,
            bytes_which_shall_be_written,
            metadata->chunk_capacity);
        return std::pair<int, file_offset_t>{write_fd_, offset_ + size};
    }
    MONAD_ABORT("zonefs support isn't implemented yet");
}

file_offset_t storage_pool::chunk::size() const
{
    if (device().is_file() || device().is_block_device()) {
        auto *metadata = device().metadata_;
        if (!append_only_) {
            // Conventional chunks are always full
            return metadata->chunk_capacity;
        }
        auto chunk_bytes_used =
            metadata->chunk_bytes_used(device().size_of_file_);
        return chunk_bytes_used[chunkid_within_device_].load(
            std::memory_order_acquire);
    }
    MONAD_ABORT("zonefs support isn't implemented yet");
}

void storage_pool::chunk::destroy_contents()
{
    if (!try_trim_contents(0)) {
        MONAD_ABORT("zonefs support isn't implemented yet");
    }
}

uint32_t storage_pool::chunk::clone_contents_into(chunk &other, uint32_t bytes)
{
    if (other.is_sequential_write() && other.size() != 0) {
        MONAD_ABORT(
            "Append only destinations must be empty before content clone");
    }
    bytes = std::min(uint32_t(size()), bytes);
    auto rdfd = read_fd();
    auto wrfd = other.write_fd(bytes);
    auto off_in = off64_t(rdfd.second);
    auto off_out = off64_t(wrfd.second);
    auto bytescopied =
        copy_file_range(rdfd.first, &off_in, wrfd.first, &off_out, bytes, 0);
    if (bytescopied == -1) {
        auto *p = aligned_alloc(DISK_PAGE_SIZE, bytes);
        MONAD_ASSERT_PRINTF(p != nullptr, "failed due to %s", strerror(errno));
        auto unp = make_scope_exit([&]() noexcept { ::free(p); });
        bytescopied =
            ::pread(rdfd.first, p, bytes, static_cast<off_t>(rdfd.second));
        MONAD_ASSERT_PRINTF(
            -1 != bytescopied, "failed due to %s", strerror(errno));
        MONAD_ASSERT_PRINTF(
            -1 != ::pwrite(
                      wrfd.first,
                      p,
                      static_cast<size_t>(bytescopied),
                      static_cast<off_t>(wrfd.second)),
            "failed due to %s",
            strerror(errno));
    }
    return uint32_t(bytescopied);
}

bool storage_pool::chunk::try_trim_contents(uint32_t bytes)
{
    bytes = std::min(uint32_t(size()), bytes);
    MONAD_DEBUG_ASSERT(capacity_ <= std::numeric_limits<off_t>::max());
    MONAD_DEBUG_ASSERT(offset_ <= std::numeric_limits<off_t>::max());
    if (device().is_file()) {
        MONAD_ASSERT_PRINTF(
            -1 != ::fallocate(
                      write_fd_,
                      FALLOC_FL_KEEP_SIZE | FALLOC_FL_PUNCH_HOLE,
                      static_cast<off_t>(offset_ + bytes),
                      static_cast<off_t>(capacity_ - bytes)),
            "failed due to %s",
            strerror(errno));
        if (append_only_) {
            auto const *metadata = device().metadata_;
            auto chunk_bytes_used =
                metadata->chunk_bytes_used(device().size_of_file_);
            chunk_bytes_used[chunkid_within_device_].store(
                bytes, std::memory_order_release);
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
        auto *buffer = reinterpret_cast<std::byte *>(
            aligned_alloc(DISK_PAGE_SIZE, DISK_PAGE_SIZE));
        auto unbuffer = make_scope_exit([&]() noexcept { ::free(buffer); });
        auto const remainder = offset_ + bytes - range[0];
        // Copy any fragment of DISK_PAGE_SIZE about to get TRIMed to a
        // temporary buffer
        auto const bytesread = (remainder == 0)
                                   ? 0
                                   : ::pread(
                                         read_fd_,
                                         buffer,
                                         DISK_PAGE_SIZE,
                                         static_cast<off_t>(range[0]));
        MONAD_ASSERT_PRINTF(
            bytesread != -1, "pread failed due to %s", strerror(errno));
        // As writes must be in DISK_PAGE_SIZE units, no point in TRIMing a
        // block only to immediately overwrite it
        if (remainder > 0) {
            range[0] += DISK_PAGE_SIZE;
            range[1] -= DISK_PAGE_SIZE;
        }
        if (range[1] > 0) {
            MONAD_DEBUG_ASSERT(
                range[0] >= offset_ && range[0] < offset_ + capacity_);
            MONAD_DEBUG_ASSERT(range[1] <= capacity_);
            MONAD_DEBUG_ASSERT((range[1] & (DISK_PAGE_SIZE - 1)) == 0);
            MONAD_ASSERT_PRINTF(
                !ioctl(write_fd_, _IO(0x12, 119) /*BLKDISCARD*/, &range),
                "failed due to %s",
                strerror(errno));
        }
        if (remainder > 0) {
            // Overwrite the final DISK_PAGE_SIZE unit with all bits after
            // truncation point set to zero
            memset(buffer + remainder, 0, DISK_PAGE_SIZE - remainder);
            MONAD_ASSERT_PRINTF(
                -1 != ::pwrite(
                          write_fd_,
                          buffer,
                          DISK_PAGE_SIZE,
                          static_cast<off_t>(range[0])),
                "failed due to %s",
                strerror(errno));
        }
        if (append_only_) {
            auto const *metadata = device().metadata_;
            auto chunk_bytes_used =
                metadata->chunk_bytes_used(device().size_of_file_);
            chunk_bytes_used[chunkid_within_device_].store(
                bytes, std::memory_order_release);
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

storage_pool::device storage_pool::make_device_(
    mode op, device::type_t_ type, std::filesystem::path const &path, int fd,
    std::variant<uint64_t, device const *> dev_no_or_dev, creation_flags flags)
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
            readwritefd != -1, "open failed due to %s", strerror(errno));
    }
    struct stat stat;
    memset(&stat, 0, sizeof(stat));
    switch (type) {
    case device::type_t_::file:
        MONAD_ASSERT_PRINTF(
            -1 != ::fstat(readwritefd, &stat),
            "failed due to %s",
            strerror(errno));
        break;
    case device::type_t_::block_device:
        MONAD_ASSERT_PRINTF(
            !ioctl(
                readwritefd,
                _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/,
                &stat.st_size),
            "failed due to %s",
            strerror(errno));
        break;
    case device::type_t_::zoned_device:
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
        auto *buffer = reinterpret_cast<std::byte *>(
            aligned_alloc(DISK_PAGE_SIZE, DISK_PAGE_SIZE * 2));
        auto unbuffer = make_scope_exit([&]() noexcept { ::free(buffer); });
        auto const offset = round_down_align<DISK_PAGE_BITS>(
            file_offset_t(stat.st_size) - sizeof(device::metadata_t));
        MONAD_DEBUG_ASSERT(offset <= std::numeric_limits<off_t>::max());
        MONAD_DEBUG_ASSERT(static_cast<size_t>(stat.st_size) > offset);
        auto const bytesread = ::pread(
            readwritefd,
            buffer,
            static_cast<size_t>(stat.st_size) - offset,
            static_cast<off_t>(offset));
        MONAD_ASSERT_PRINTF(
            bytesread != -1, "pread failed due to %s", strerror(errno));
        auto *metadata_footer = start_lifetime_as<device::metadata_t>(
            buffer + bytesread - sizeof(device::metadata_t));
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
            case device::type_t_::file:
                MONAD_ASSERT_PRINTF(
                    ::ftruncate(readwritefd, 0) != -1,
                    "failed due to %s",
                    strerror(errno));
                MONAD_ASSERT_PRINTF(
                    ::ftruncate(readwritefd, stat.st_size) != -1,
                    "failed due to %s",
                    strerror(errno));
                break;
            case device::type_t_::block_device: {
                uint64_t range[2] = {0, uint64_t(stat.st_size)};
                if (ioctl(readwritefd, _IO(0x12, 119) /*BLKDISCARD*/, &range)) {
                    MONAD_ABORT_PRINTF(
                        "ioctl failed due to %s", strerror(errno));
                }
                break;
            }
            case device::type_t_::zoned_device:
                MONAD_ABORT("zonefs support isn't implemented yet");
            default:
                abort();
            }
            memset(buffer, 0, DISK_PAGE_SIZE * 2);
            MONAD_DEBUG_ASSERT(
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
                    strerror(errno));
            }
            memcpy(metadata_footer->magic, "MND0", 4);
            metadata_footer->chunk_capacity =
                static_cast<uint32_t>(chunk_capacity);
            MONAD_ASSERT_PRINTF(
                ::pwrite(
                    readwritefd,
                    buffer,
                    static_cast<size_t>(bytesread),
                    static_cast<off_t>(offset)) > 0,
                "failed due to %s",
                strerror(errno));
        }
        total_size =
            metadata_footer->total_size(static_cast<size_t>(stat.st_size));
    }
    auto offset = round_down_align<CPU_PAGE_BITS>(
        static_cast<size_t>(stat.st_size) - total_size);
    auto bytestomap = round_up_align<CPU_PAGE_BITS>(
        static_cast<size_t>(stat.st_size) - offset);
    auto *addr = ::mmap(
        nullptr,
        bytestomap,
        (flags.open_read_only && !flags.open_read_only_allow_dirty)
            ? (PROT_READ)
            : (PROT_READ | PROT_WRITE),
        flags.open_read_only_allow_dirty ? MAP_PRIVATE : MAP_SHARED,
        readwritefd,
        static_cast<off_t>(offset));
    MONAD_ASSERT_PRINTF(
        MAP_FAILED != addr, "mmap failed due to %s", strerror(errno));
    auto *metadata = start_lifetime_as<device::metadata_t>(
        reinterpret_cast<std::byte *>(addr) + stat.st_size - offset -
        sizeof(device::metadata_t));
    MONAD_DEBUG_ASSERT(0 == memcmp(metadata->magic, "MND0", 4));
    if (auto const **dev = std::get_if<1>(&dev_no_or_dev)) {
        unique_hash = (*dev)->unique_hash_;
    }
    return device(
        readwritefd,
        type,
        unique_hash,
        static_cast<size_t>(stat.st_size),
        metadata);
}

void storage_pool::fill_chunks_(creation_flags const &flags)
{
    (void)flags;
    auto hashshouldbe = fnv1a_hash<uint32_t>::begin();
    for (auto &device : devices_) {
        fnv1a_hash<uint32_t>::add(hashshouldbe, uint32_t(device.unique_hash_));
        fnv1a_hash<uint32_t>::add(
            hashshouldbe, uint32_t(device.unique_hash_ >> 32));
    }
    std::vector<size_t> chunks;
    size_t total = 0;
    chunks.reserve(devices_.size());
    for (auto const &device : devices_) {
        if (device.is_file() || device.is_block_device()) {
            auto const devicechunks = device.chunks();
            MONAD_ASSERT_PRINTF(
                devicechunks >= 4,
                "Device %s has %zu chunks the minimum allowed is four.",
                device.current_path().c_str(),
                devicechunks);
            MONAD_DEBUG_ASSERT(
                devicechunks <= std::numeric_limits<uint32_t>::max());
            // Take off three for the cnv chunks
            chunks.push_back(devicechunks - 3);
            total += devicechunks - 3;
            fnv1a_hash<uint32_t>::add(
                hashshouldbe, static_cast<uint32_t>(devicechunks));
            fnv1a_hash<uint32_t>::add(
                hashshouldbe, device.metadata_->chunk_capacity);
        }
        else {
            MONAD_ABORT("zonefs support isn't implemented yet");
        }
    }
    for (auto const &device : devices_) {
        if (device.metadata_->config_hash == 0) {
            device.metadata_->config_hash = uint32_t(hashshouldbe);
        }
        else if (device.metadata_->config_hash != uint32_t(hashshouldbe)) {
            std::stringstream str;
            if (!flags.disable_mismatching_storage_pool_check) {
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s was initialised with a "
                    "configuration different to this storage pool. Is a device "
                    "missing or is there an extra device from when the pool "
                    "was first created?\n\nYou should use the monad_mpt tool "
                    "to copy and move databases around, NOT by copying "
                    "partition contents!",
                    device.current_path().c_str());
            }
            else {
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s was initialised with a "
                    "configuration different to this storage pool. Is a device "
                    "missing or is there an extra device from when the pool "
                    "was first created?\n\nYou should use the monad_mpt tool "
                    "to copy and move databases around, NOT by copying "
                    "partition contents!\n\nSince the monad_mpt tool was "
                    "added, the flag disable_mismatching_storage_pool_check is "
                    "no longer needed and has been disabled.",
                    device.current_path().c_str());
            }
        }
    }
    // First three blocks of each device goes to conventional, remainder go to
    // sequential
    chunks_[cnv].reserve(devices_.size() * 3);
    chunks_[seq].reserve(total);
    if (flags.interleave_chunks_evenly) {
        for (auto &device : devices_) {
            chunks_[cnv].emplace_back(std::weak_ptr<class chunk>{}, device, 0);
        }
        for (auto &device : devices_) {
            chunks_[cnv].emplace_back(std::weak_ptr<class chunk>{}, device, 1);
        }
        for (auto &device : devices_) {
            chunks_[cnv].emplace_back(std::weak_ptr<class chunk>{}, device, 2);
        }
        // We now need to evenly spread the sequential chunks such that if
        // device A has 20, device B has 10 and device C has 5, the interleaving
        // would be ABACABA i.e. a ratio of 4:2:1
        std::vector<double> chunkratios(chunks.size());
        std::vector<double> chunkcounts(chunks.size());
        for (size_t n = 0; n < chunks.size(); n++) {
            chunkratios[n] = double(total) / static_cast<double>(chunks[n]);
            chunkcounts[n] = chunkratios[n];
            chunks[n] = 3;
        }
        while (chunks_[seq].size() < chunks_[seq].capacity()) {
            for (size_t n = 0; n < chunks.size(); n++) {
                chunkcounts[n] -= 1.0;
                if (chunkcounts[n] < 0) {
                    chunks_[seq].emplace_back(
                        std::weak_ptr<class chunk>{}, devices_[n], chunks[n]++);
                    chunkcounts[n] += chunkratios[n];
                    if (chunks_[seq].size() == chunks_[seq].capacity()) {
                        break;
                    }
                }
            }
        }
#ifndef NDEBUG
        for (size_t n = 0; n < chunks.size(); n++) {
            auto devicechunks = devices_[n].chunks();
            MONAD_DEBUG_ASSERT(chunks[n] == devicechunks);
        }
#endif
    }
    else {
        for (auto &device : devices_) {
            chunks_[cnv].emplace_back(std::weak_ptr<class chunk>{}, device, 0);
            chunks_[cnv].emplace_back(std::weak_ptr<class chunk>{}, device, 1);
            chunks_[cnv].emplace_back(std::weak_ptr<class chunk>{}, device, 2);
        }
        for (size_t deviceidx = 0; deviceidx < chunks.size(); deviceidx++) {
            for (size_t n = 0; n < chunks[deviceidx]; n++) {
                chunks_[seq].emplace_back(
                    std::weak_ptr<class chunk>{}, devices_[deviceidx], 3 + n);
            }
        }
    }
}

storage_pool::storage_pool(storage_pool const *src, clone_as_read_only_tag_)
    : is_read_only_(true)
    , is_read_only_allow_dirty_(false)
    , is_newly_truncated_(false)
{
    devices_.reserve(src->devices_.size());
    creation_flags flags;
    flags.open_read_only = true;
    for (auto const &src_device : src->devices_) {
        devices_.push_back([&] {
            auto const path = src_device.current_path();
            int const fd = [&] {
                if (!path.empty()) {
                    return ::open(path.c_str(), O_PATH | O_CLOEXEC);
                }
                char path[PATH_MAX];
                sprintf(path, "/proc/self/fd/%d", src_device.readwritefd_);
                return ::open(path, O_RDONLY | O_CLOEXEC);
            }();
            MONAD_ASSERT_PRINTF(
                fd != -1, "open failed due to %s", strerror(errno));
            auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
            if (path.empty()) {
                unfd.release();
            }
            if (src_device.is_block_device()) {
                return make_device_(
                    mode::open_existing,
                    device::type_t_::block_device,
                    path,
                    fd,
                    &src_device,
                    flags);
            }
            if (src_device.is_file()) {
                return make_device_(
                    mode::open_existing,
                    device::type_t_::file,
                    path,
                    fd,
                    &src_device,
                    flags);
            }
            if (src_device.is_zoned_device()) {
                MONAD_ABORT("zonefs support isn't actually implemented yet");
            }
            MONAD_ABORT();
        }());
    }
    fill_chunks_(flags);
}

storage_pool::storage_pool(
    std::span<std::filesystem::path const> sources, mode mode,
    creation_flags flags)
    : is_read_only_(flags.open_read_only || flags.open_read_only_allow_dirty)
    , is_read_only_allow_dirty_(flags.open_read_only_allow_dirty)
    , is_newly_truncated_(mode == mode::truncate)
{
    devices_.reserve(sources.size());
    for (auto const &source : sources) {
        devices_.push_back([&] {
            int const fd = ::open(source.c_str(), O_PATH | O_CLOEXEC);
            MONAD_ASSERT_PRINTF(
                fd != -1, "open failed due to %s", strerror(errno));
            auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
            struct statfs statfs;
            MONAD_ASSERT_PRINTF(
                -1 != ::fstatfs(fd, &statfs),
                "failed due to %s",
                strerror(errno));
            MONAD_ASSERT(
                statfs.f_type != 0x5a4f4653 /*ZONEFS_MAGIC*/,
                "zonefs support isn't actually implemented yet");
            struct stat stat;
            MONAD_ASSERT_PRINTF(
                -1 != ::fstat(fd, &stat), "failed due to %s", strerror(errno));
            if ((stat.st_mode & S_IFMT) == S_IFBLK) {
                return make_device_(
                    mode,
                    device::type_t_::block_device,
                    source.c_str(),
                    fd,
                    0ULL,
                    flags);
            }
            if ((stat.st_mode & S_IFMT) == S_IFREG) {
                return make_device_(
                    mode,
                    device::type_t_::file,
                    source.c_str(),
                    fd,
                    stat.st_ino,
                    flags);
            }
            MONAD_ABORT_PRINTF(
                "Storage pool source %s has unknown file entry type = %u",
                source.string().c_str(),
                stat.st_mode & S_IFMT);
        }());
    }
    fill_chunks_(flags);
}

storage_pool::storage_pool(use_anonymous_inode_tag, creation_flags flags)
    : storage_pool::storage_pool(
          use_anonymous_sized_inode_tag{},
          1ULL * 1024 * 1024 * 1024 * 1024 + 24576, flags)
{
}

storage_pool::storage_pool(
    use_anonymous_sized_inode_tag, off_t len, creation_flags flags)
    : is_read_only_(flags.open_read_only || flags.open_read_only_allow_dirty)
    , is_read_only_allow_dirty_(flags.open_read_only_allow_dirty)
    , is_newly_truncated_(false)
{
    int const fd = make_temporary_inode();
    auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    MONAD_ASSERT_PRINTF(
        -1 != ::ftruncate(fd, len), "failed due to %s", strerror(errno));
    devices_.push_back(make_device_(
        mode::truncate, device::type_t_::file, {}, fd, uint64_t(0), flags));
    unfd.release();
    fill_chunks_(flags);
}

storage_pool::~storage_pool()
{
    auto cleanupchunks_ = [&](chunk_type which) {
        for (auto &chunk_ : chunks_[which]) {
            auto chunk(chunk_.chunk.lock());
            if (chunk && (chunk->owns_readfd_ || chunk->owns_writefd_)) {
                auto fd = chunk->read_fd_;
                if (chunk->owns_readfd_ && chunk->read_fd_ != -1) {
                    (void)::close(chunk->read_fd_);
                    chunk->read_fd_ = -1;
                }
                if (chunk->owns_writefd_ && chunk->write_fd_ != -1) {
                    if (chunk->write_fd_ != fd) {
                        (void)::fsync(chunk->write_fd_);
                        (void)::close(chunk->write_fd_);
                    }
                    chunk->write_fd_ = -1;
                }
            }
        }
        chunks_[which].clear();
    };
    cleanupchunks_(cnv);
    cleanupchunks_(seq);
    for (auto &device : devices_) {
        if (device.metadata_ != nullptr) {
            auto total_size =
                device.metadata_->total_size(device.size_of_file_);
            ::munmap(
                reinterpret_cast<void *>(round_down_align<CPU_PAGE_BITS>(
                    (uintptr_t)device.metadata_ + sizeof(device::metadata_t) -
                    total_size)),
                total_size);
        }
        if (device.readwritefd_ != -1) {
            (void)::fsync(device.readwritefd_);
            (void)::close(device.readwritefd_);
        }
    }
    devices_.clear();
}

size_t storage_pool::currently_active_chunks(chunk_type which) const noexcept
{
    std::unique_lock const g(lock_);
    size_t ret = 0;
    for (auto const &i : chunks_[which]) {
        if (!i.chunk.expired()) {
            ret++;
        }
    }
    return ret;
}

std::shared_ptr<class storage_pool::chunk>
storage_pool::chunk(chunk_type which, uint32_t id) const
{
    std::unique_lock const g(lock_);
    if (id >= chunks_[which].size()) {
        MONAD_ABORT("Requested chunk which does not exist");
    }
    return chunks_[which][id].chunk.lock();
}

std::shared_ptr<class storage_pool::chunk>
storage_pool::activate_chunk(chunk_type const which, uint32_t const id)
{
#ifndef __clang__
    MONAD_DEBUG_ASSERT(this != nullptr);
#endif
    std::unique_lock g(lock_);
    if (id >= chunks_[which].size()) {
        MONAD_ABORT("Requested to activate chunk which does not exist");
    }
    auto ret = chunks_[which][id].chunk.lock();
    if (ret) {
        return ret;
    }
    g.unlock();
    auto &chunkinfo = chunks_[which][id];
    switch (which) {
    case chunk_type::cnv:
        ret = std::shared_ptr<cnv_chunk>(new cnv_chunk(
            chunkinfo.device,
            chunkinfo.device.readwritefd_,
            chunkinfo.device.readwritefd_,
            file_offset_t(chunkinfo.chunk_offset_into_device) *
                chunkinfo.device.metadata_->chunk_capacity,
            chunkinfo.device.metadata_->chunk_capacity,
            chunkinfo.chunk_offset_into_device,
            id,
            false,
            false,
            false));
        break;
    case chunk_type::seq: {
        ret = std::shared_ptr<seq_chunk>(new seq_chunk(
            chunkinfo.device,
            chunkinfo.device.readwritefd_,
            chunkinfo.device.readwritefd_,
            file_offset_t(chunkinfo.chunk_offset_into_device) *
                chunkinfo.device.metadata_->chunk_capacity,
            chunkinfo.device.metadata_->chunk_capacity,
            chunkinfo.chunk_offset_into_device,
            id,
            false,
            false,
            true));
        break;
    }
    }
    MONAD_ASSERT(ret);
    if (ret->device().is_zoned_device()) {
        MONAD_ABORT("zonefs support isn't implemented yet");
    }
    g.lock();
    auto ret2 = chunks_[which][id].chunk.lock();
    if (ret2) {
        return ret2;
    }
    chunks_[which][id].chunk = ret;
    return ret;
}

storage_pool storage_pool::clone_as_read_only() const
{
    return storage_pool(this, clone_as_read_only_tag_{});
}

MONAD_ASYNC_NAMESPACE_END
