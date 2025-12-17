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
#include <category/async/detail/start_lifetime_as_polyfill.hpp>
#include <category/async/util.hpp>
#include <category/core/assert.h>
#include <category/core/hash.hpp>

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
#include <mutex>
#include <span>
#include <utility>
#include <variant>
#include <vector>

#include <stdlib.h>

#include <quill/Quill.h>

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
    return metadata_->num_cnv_chunks;
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
        auto const useds = metadata_->chunk_bytes_used(size_of_file_);
        for (size_t n = 0; n < chunks; n++) {
            used += useds[n].load(std::memory_order_acquire);
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

storage_pool::chunk_t::~chunk_t()
{
    if (owns_readfd_ || owns_writefd_) {
        auto const fd = read_fd_;
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
storage_pool::chunk_t::write_fd(size_t bytes_which_shall_be_written) noexcept
{
    if (device().is_file() || device().is_block_device()) {
        if (!append_only_) {
            return std::pair<int, file_offset_t>{write_fd_, offset_};
        }
        auto const *const metadata = device().metadata_;
        auto const chunk_bytes_used =
            metadata->chunk_bytes_used(device().size_of_file_);
        MONAD_ASSERT(
            bytes_which_shall_be_written <=
            std::numeric_limits<uint32_t>::max());
        auto const size =
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

file_offset_t storage_pool::chunk_t::size() const
{
    if (device().is_file() || device().is_block_device()) {
        auto *const metadata = device().metadata_;
        if (!append_only_) {
            // Conventional chunks are always full
            return metadata->chunk_capacity;
        }
        auto const chunk_bytes_used =
            metadata->chunk_bytes_used(device().size_of_file_);
        return chunk_bytes_used[chunkid_within_device_].load(
            std::memory_order_acquire);
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
                      write_fd_,
                      FALLOC_FL_KEEP_SIZE | FALLOC_FL_PUNCH_HOLE,
                      static_cast<off_t>(offset_ + bytes),
                      static_cast<off_t>(capacity_ - bytes)),
            "failed due to %s",
            std::strerror(errno));
        if (append_only_) {
            auto const *metadata = device().metadata_;
            auto const chunk_bytes_used =
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
                          read_fd_,
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
                          write_fd_,
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
                !ioctl(write_fd_, _IO(0x12, 119) /*BLKDISCARD*/, &range),
                "failed due to %s",
                std::strerror(errno));
        }
        if (append_only_) {
            auto const *metadata = device().metadata_;
            auto const chunk_bytes_used =
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

storage_pool::device_t storage_pool::make_device_(
    mode op, device_t::type_t_ type, std::filesystem::path const &path, int fd,
    std::variant<uint64_t, device_t const *> dev_no_or_dev,
    creation_flags flags)
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
        if (flags.num_cnv_chunks > metadata_footer->num_cnv_chunks) {
            LOG_WARNING(
                "Flag-specified num_cnv_chunks ({}) is greater than the value "
                "stored in metadata ({}). This setting will be ignored. "
                "Existing databases cannot be reconfigured to use more chunks, "
                "create a new database if you need a higher num_cnv_chunks.",
                flags.num_cnv_chunks,
                metadata_footer->num_cnv_chunks == 0
                    ? 3
                    : metadata_footer->num_cnv_chunks);
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

void storage_pool::fill_chunks_(creation_flags const &flags)
{
    auto hashshouldbe = fnv1a_hash<uint32_t>::begin();
    for (auto const &device : devices_) {
        fnv1a_hash<uint32_t>::add(hashshouldbe, uint32_t(device.unique_hash_));
        fnv1a_hash<uint32_t>::add(
            hashshouldbe, uint32_t(device.unique_hash_ >> 32));
    }
    // Backward compatibility: databases created before `num_cnv_chunks` was
    // added have this field set to 0. Treat 0 as the legacy default of 3
    // chunks.
    uint32_t const cnv_chunks_count =
        devices_[0].metadata_->num_cnv_chunks == 0
            ? 3
            : devices_[0].metadata_->num_cnv_chunks;
    std::vector<size_t> chunks;
    size_t total = 0;
    chunks.reserve(devices_.size());
    for (auto const &device : devices_) {
        if (device.is_file() || device.is_block_device()) {
            auto const devicechunks = device.chunks();
            MONAD_ASSERT_PRINTF(
                devicechunks >= cnv_chunks_count + 1,
                "Device %s has %zu chunks the minimum allowed is %u.",
                device.current_path().c_str(),
                devicechunks,
                cnv_chunks_count + 1);
            MONAD_ASSERT(devicechunks <= std::numeric_limits<uint32_t>::max());
            // Take off cnv_chunks_count for the cnv chunks
            chunks.push_back(devicechunks - cnv_chunks_count);
            total += devicechunks - cnv_chunks_count;
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
            if (!flags.disable_mismatching_storage_pool_check) {
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s was initialised with a "
                    "configuration different to this storage pool. Is a device "
                    "missing or is there an extra device from when the pool "
                    "was first created?\n\nYou should use the monad-mpt tool "
                    "to copy and move databases around, NOT by copying "
                    "partition contents!",
                    device.current_path().c_str());
            }
            else {
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s was initialised with a "
                    "configuration different to this storage pool. Is a device "
                    "missing or is there an extra device from when the pool "
                    "was first created?\n\nYou should use the monad-mpt tool "
                    "to copy and move databases around, NOT by copying "
                    "partition contents!\n\nSince the monad-mpt tool was "
                    "added, the flag disable_mismatching_storage_pool_check is "
                    "no longer needed and has been disabled.",
                    device.current_path().c_str());
            }
        }
    }
    auto const zone_id = [this](int const chunk_type) {
        return static_cast<uint32_t>(chunks_[chunk_type].size());
    };
    // First cnv_chunks_count blocks of each device goes to conventional,
    // remainder go to sequential
    chunks_[cnv].reserve(devices_.size() * cnv_chunks_count);
    chunks_[seq].reserve(total);
    if (flags.interleave_chunks_evenly) {
        for (uint32_t chunk_idx = 0; chunk_idx < cnv_chunks_count;
             ++chunk_idx) {
            for (auto &device : devices_) {
                chunks_[cnv].emplace_back(activate_chunk(
                    storage_pool::cnv, device, chunk_idx, zone_id(cnv)));
            }
        }
        // We now need to evenly spread the sequential chunks such that if
        // device A has 20, device B has 10 and device C has 5, the interleaving
        // would be ABACABA i.e. a ratio of 4:2:1
        std::vector<double> chunkratios(chunks.size());
        std::vector<double> chunkcounts(chunks.size());
        for (size_t n = 0; n < chunks.size(); n++) {
            chunkratios[n] = double(total) / static_cast<double>(chunks[n]);
            chunkcounts[n] = chunkratios[n];
            chunks[n] = cnv_chunks_count;
        }
        while (chunks_[seq].size() < chunks_[seq].capacity()) {
            for (size_t n = 0; n < chunks.size(); n++) {
                chunkcounts[n] -= 1.0;
                if (chunkcounts[n] < 0) {
                    chunks_[seq].emplace_back(activate_chunk(
                        seq,
                        devices_[n],
                        static_cast<uint32_t>(chunks[n]++),
                        zone_id(seq)));
                    chunkcounts[n] += chunkratios[n];
                    if (chunks_[seq].size() == chunks_[seq].capacity()) {
                        break;
                    }
                }
            }
        }
#ifndef NDEBUG
        for (size_t n = 0; n < chunks.size(); n++) {
            auto const devicechunks = devices_[n].chunks();
            MONAD_ASSERT(chunks[n] == devicechunks);
        }
#endif
    }
    else {
        for (auto &device : devices_) {
            for (uint32_t chunk_idx = 0; chunk_idx < cnv_chunks_count;
                 ++chunk_idx) {
                chunks_[cnv].emplace_back(
                    activate_chunk(cnv, device, chunk_idx, zone_id(cnv)));
            }
        }
        for (size_t deviceidx = 0; deviceidx < chunks.size(); deviceidx++) {
            for (size_t n = 0; n < chunks[deviceidx]; n++) {
                chunks_[seq].emplace_back(activate_chunk(
                    seq,
                    devices_[deviceidx],
                    static_cast<uint32_t>(cnv_chunks_count + n),
                    zone_id(seq)));
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
                fd != -1, "open failed due to %s", std::strerror(errno));
            auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
            if (path.empty()) {
                unfd.release();
            }
            if (src_device.is_block_device()) {
                return make_device_(
                    mode::open_existing,
                    device_t::type_t_::block_device,
                    path,
                    fd,
                    &src_device,
                    flags);
            }
            if (src_device.is_file()) {
                return make_device_(
                    mode::open_existing,
                    device_t::type_t_::file,
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
                fd != -1, "open failed due to %s", std::strerror(errno));
            auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
            struct statfs statfs;
            MONAD_ASSERT_PRINTF(
                -1 != ::fstatfs(fd, &statfs),
                "failed due to %s",
                std::strerror(errno));
            MONAD_ASSERT(
                statfs.f_type != 0x5a4f4653 /*ZONEFS_MAGIC*/,
                "zonefs support isn't actually implemented yet");
            struct stat stat;
            MONAD_ASSERT_PRINTF(
                -1 != ::fstat(fd, &stat),
                "failed due to %s",
                std::strerror(errno));
            if ((stat.st_mode & S_IFMT) == S_IFBLK) {
                return make_device_(
                    mode,
                    device_t::type_t_::block_device,
                    source.c_str(),
                    fd,
                    0ULL,
                    flags);
            }
            if ((stat.st_mode & S_IFMT) == S_IFREG) {
                return make_device_(
                    mode,
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
        -1 != ::ftruncate(fd, len), "failed due to %s", std::strerror(errno));
    devices_.push_back(make_device_(
        mode::truncate, device_t::type_t_::file, {}, fd, uint64_t(0), flags));
    unfd.release();
    fill_chunks_(flags);
}

storage_pool::~storage_pool()
{
    auto const cleanupchunks_ = [&](chunk_type which) {
        for (auto &chunk : chunks_[which]) {
            if (chunk.owns_readfd_ || chunk.owns_writefd_) {
                auto const fd = chunk.read_fd_;
                if (chunk.owns_readfd_ && chunk.read_fd_ != -1) {
                    (void)::close(chunk.read_fd_);
                    chunk.read_fd_ = -1;
                }
                if (chunk.owns_writefd_ && chunk.write_fd_ != -1) {
                    if (chunk.write_fd_ != fd) {
                        (void)::fsync(chunk.write_fd_);
                        (void)::close(chunk.write_fd_);
                    }
                    chunk.write_fd_ = -1;
                }
            }
        }
        chunks_[which].clear();
    };
    cleanupchunks_(cnv);
    cleanupchunks_(seq);
    for (auto const &device : devices_) {
        if (device.metadata_ != nullptr) {
            auto const total_size =
                device.metadata_->total_size(device.size_of_file_);
            ::munmap(
                reinterpret_cast<void *>(round_down_align<CPU_PAGE_BITS>(
                    (uintptr_t)device.metadata_ + sizeof(device_t::metadata_t) -
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

storage_pool::chunk_t &storage_pool::chunk(chunk_type which, uint32_t id)
{
    std::unique_lock const g(lock_);
    if (id >= chunks_[which].size()) {
        MONAD_ABORT("Requested chunk which does not exist");
    }
    return chunks_[which][id];
}

storage_pool::chunk_t storage_pool::activate_chunk(
    chunk_type const which, device_t &device, uint32_t const id_within_device,
    uint32_t const id_within_zone)
{
#ifndef __clang__
    MONAD_ASSERT(this != nullptr);
#endif
    std::unique_lock const g(lock_);
    chunk_t const ret = [&]() {
        switch (which) {
        case chunk_type::cnv:
            return chunk_t{
                device,
                device.readwritefd_,
                device.readwritefd_,
                file_offset_t(id_within_device) *
                    device.metadata_->chunk_capacity,
                device.metadata_->chunk_capacity,
                id_within_device,
                id_within_zone,
                false,
                false,
                false};
        case chunk_type::seq: {
            return chunk_t{
                device,
                device.readwritefd_,
                device.readwritefd_,
                file_offset_t(id_within_device) *
                    device.metadata_->chunk_capacity,
                device.metadata_->chunk_capacity,
                id_within_device,
                id_within_zone,
                false,
                false,
                true};
        }
        }
        MONAD_ABORT_PRINTF("chunk type not supported: %d", which);
    }();
    MONAD_ASSERT_PRINTF(
        !ret.device().is_zoned_device(), "zonefs isn't implemented");
    return ret;
}

storage_pool storage_pool::clone_as_read_only() const
{
    return storage_pool(this, clone_as_read_only_tag_{});
}

MONAD_ASYNC_NAMESPACE_END
