
#include <category/async/storage_pool.hpp>

#include <category/async/detail/scope_polyfill.hpp>
#include <monad/core/assert.h>
#include <monad/core/hash.hpp>

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
    snprintf(in, sizeof(in), "/proc/self/fd/%d", cached_readwritefd_);
    ssize_t len;
    if ((len = ::readlink(in, out, 32768)) == -1) {
        throw std::system_error(errno, std::system_category());
    }
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
    if (is_zoned_device()) {
        throw std::runtime_error("zonefs support isn't implemented yet");
    }
    return metadata_->chunks(size_of_file_);
}

std::pair<file_offset_t, file_offset_t> storage_pool::device::capacity() const
{
    switch (type_) {
    case device::type_t_::file: {
        struct stat stat;
        if (-1 == ::fstat(cached_readwritefd_, &stat)) {
            throw std::system_error(errno, std::system_category());
        }
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
        if (ioctl(
                cached_readwritefd_,
                _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/,
                &capacity)) {
            throw std::system_error(errno, std::system_category());
        }
        auto const chunks = this->chunks();
        auto const useds = metadata_->chunk_bytes_used(size_of_file_);
        for (size_t n = 0; n < chunks; n++) {
            used += useds[n].load(std::memory_order_acquire);
        }
        return {capacity, used};
    }
    case device::type_t_::zoned_device:
        throw std::runtime_error("zonefs support isn't implemented yet");
    default:
        abort();
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
    throw std::runtime_error("zonefs support isn't implemented yet");
}

void storage_pool::chunk::destroy_contents()
{
    if (!try_trim_contents(0)) {
        throw std::runtime_error("zonefs support isn't implemented yet");
    }
}

uint32_t storage_pool::chunk::clone_contents_into(chunk &other, uint32_t bytes)
{
    if (other.is_sequential_write() && other.size() != 0) {
        throw std::runtime_error(
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
        if (-1 == ::fallocate(
                      write_fd_,
                      FALLOC_FL_KEEP_SIZE | FALLOC_FL_PUNCH_HOLE,
                      static_cast<off_t>(offset_ + bytes),
                      static_cast<off_t>(capacity_ - bytes))) {
            throw std::system_error(errno, std::system_category());
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
        if (-1 == bytesread) {
            throw std::system_error(errno, std::system_category());
        }
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
            if (ioctl(write_fd_, _IO(0x12, 119) /*BLKDISCARD*/, &range)) {
                throw std::system_error(errno, std::system_category());
            }
        }
        if (remainder > 0) {
            // Overwrite the final DISK_PAGE_SIZE unit with all bits after
            // truncation point set to zero
            memset(buffer + remainder, 0, DISK_PAGE_SIZE - remainder);
            if (-1 == ::pwrite(
                          write_fd_,
                          buffer,
                          DISK_PAGE_SIZE,
                          static_cast<off_t>(range[0]))) {
                throw std::system_error(errno, std::system_category());
            }
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
        if (-1 == readwritefd) {
            throw std::system_error(errno, std::system_category());
        }
    }
    struct stat stat;
    memset(&stat, 0, sizeof(stat));
    switch (type) {
    case device::type_t_::file:
        if (-1 == ::fstat(readwritefd, &stat)) {
            throw std::system_error(errno, std::system_category());
        }
        break;
    case device::type_t_::block_device:
        if (ioctl(
                readwritefd,
                _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/,
                &stat.st_size)) {
            throw std::system_error(errno, std::system_category());
        }
        break;
    case device::type_t_::zoned_device:
        throw std::runtime_error("zonefs support isn't implemented yet");
    default:
        abort();
    }
    if (stat.st_size < CPU_PAGE_SIZE) {
        std::stringstream str;
        str << "Storage pool source " << path
            << " must be at least 4Kb long to be used with "
               "storage "
               "pool";
        throw std::runtime_error(std::move(str).str());
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
        if (-1 == bytesread) {
            throw std::system_error(errno, std::system_category());
        }
        auto *metadata_footer = start_lifetime_as<device::metadata_t>(
            buffer + bytesread - sizeof(device::metadata_t));
        if (memcmp(metadata_footer->magic, "MND0", 4) != 0 ||
            op == mode::truncate) {
            // Uninitialised
            if (op == mode::open_existing) {
                std::stringstream str;
                str << "Storage pool source " << path
                    << " has not been initialised for use with storage pool";
                throw std::runtime_error(std::move(str).str());
            }
            if (stat.st_size < (1LL << flags.chunk_capacity) + CPU_PAGE_SIZE) {
                std::stringstream str;
                str << "Storage pool source " << path
                    << " must be at least chunk_capacity + 4Kb long to be "
                       "initialised "
                       "for use with storage pool";
                throw std::runtime_error(std::move(str).str());
            }
            // Throw away all contents
            switch (type) {
            case device::type_t_::file:
                if (-1 == ::ftruncate(readwritefd, 0)) {
                    throw std::system_error(errno, std::system_category());
                }
                if (-1 == ::ftruncate(readwritefd, stat.st_size)) {
                    throw std::system_error(errno, std::system_category());
                }
                break;
            case device::type_t_::block_device: {
                uint64_t range[2] = {0, uint64_t(stat.st_size)};
                if (ioctl(readwritefd, _IO(0x12, 119) /*BLKDISCARD*/, &range)) {
                    throw std::system_error(errno, std::system_category());
                }
                break;
            }
            case device::type_t_::zoned_device:
                throw std::runtime_error(
                    "zonefs support isn't implemented yet");
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
    if (MAP_FAILED == addr) {
        throw std::system_error(errno, std::system_category());
    }
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
            if (devicechunks < 4) {
                throw std::runtime_error(std::format(
                    "Device {} has {} chunks the minimum allowed is four.",
                    device.current_path().c_str(),
                    devicechunks));
            }
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
            throw std::runtime_error("zonefs support isn't implemented yet");
        }
    }
    for (auto const &device : devices_) {
        if (device.metadata_->config_hash == 0) {
            device.metadata_->config_hash = uint32_t(hashshouldbe);
        }
        else if (device.metadata_->config_hash != uint32_t(hashshouldbe)) {
            std::stringstream str;
            if (!flags.disable_mismatching_storage_pool_check) {
                str << "Storage pool source " << device.current_path()
                    << " was initialised with a configuration different to "
                       "this storage pool. Is a device missing or is there an "
                       "extra device from when the pool was first "
                       "created?\n\nYou should use the monad_mpt tool to copy "
                       "and move databases around, NOT by copying partition "
                       "contents!";
                throw std::runtime_error(std::move(str).str());
            }
            else {
                str << "Storage pool source " << device.current_path()
                    << " was initialised with a configuration different to "
                       "this storage pool. Is a device missing or is there an "
                       "extra device from when the pool was first "
                       "created?\n\nYou should use the monad_mpt tool to copy "
                       "and move databases around, NOT by copying partition "
                       "contents\n\nSince the monad_mpt tool was added, the "
                       "flag disable_mismatching_storage_pool_check is no "
                       "longer needed and has been disabled.";
                throw std::runtime_error(std::move(str).str());
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
                sprintf(
                    path, "/proc/self/fd/%d", src_device.cached_readwritefd_);
                return ::open(path, O_RDONLY | O_CLOEXEC);
            }();
            if (-1 == fd) {
                throw std::system_error(errno, std::system_category());
            }
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
                throw std::runtime_error(
                    "zonefs support isn't actually implemented yet");
            }
            abort();
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
            if (-1 == fd) {
                throw std::system_error(errno, std::system_category());
            }
            auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
            struct statfs statfs;
            if (-1 == ::fstatfs(fd, &statfs)) {
                throw std::system_error(errno, std::system_category());
            }
            if (statfs.f_type == 0x5a4f4653 /*ZONEFS_MAGIC*/) {
                throw std::runtime_error(
                    "zonefs support isn't actually implemented yet");
            }
            struct stat stat;
            if (-1 == ::fstat(fd, &stat)) {
                throw std::system_error(errno, std::system_category());
            }
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
            std::stringstream str;
            str << "Storage pool source " << source
                << " has unknown file entry type = " << (stat.st_mode & S_IFMT);
            throw std::runtime_error(std::move(str).str());
        }());
    }
    fill_chunks_(flags);
}

storage_pool::storage_pool(use_anonymous_inode_tag, creation_flags flags)
    : is_read_only_(flags.open_read_only || flags.open_read_only_allow_dirty)
    , is_read_only_allow_dirty_(flags.open_read_only_allow_dirty)
    , is_newly_truncated_(false)
{
    int const fd = make_temporary_inode();
    auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    if (-1 ==
        ::ftruncate(fd, 1ULL * 1024 * 1024 * 1024 * 1024 + 24576 /* 1Tb */)) {
        throw std::system_error(errno, std::system_category());
    }
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
        if (device.uncached_readfd_ != -1) {
            (void)::close(device.uncached_readfd_);
        }
        if (device.uncached_writefd_ != -1) {
            (void)::fsync(device.uncached_writefd_);
            (void)::close(device.uncached_writefd_);
        }
        if (device.cached_readwritefd_ != -1) {
            (void)::fsync(device.cached_readwritefd_);
            (void)::close(device.cached_readwritefd_);
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
        throw std::runtime_error("Requested chunk which does not exist");
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
        throw std::runtime_error(
            "Requested to activate chunk which does not exist");
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
            chunkinfo.device.cached_readwritefd_,
            chunkinfo.device.cached_readwritefd_,
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
        int fds[2] = {
            chunkinfo.device.uncached_readfd_,
            chunkinfo.device.uncached_writefd_};
        if (-1 == fds[0]) {
            auto devicepath = chunkinfo.device.current_path();
            if (!devicepath.empty()) {
                fds[0] = chunkinfo.device.uncached_readfd_ =
                    ::open(devicepath.c_str(), O_RDONLY | O_DIRECT | O_CLOEXEC);
                if (-1 == fds[0]) {
                    throw std::system_error(errno, std::system_category());
                }
                fds[1] = chunkinfo.device.uncached_writefd_ = ::open(
                    devicepath.c_str(),
                    (is_read_only() ? O_RDONLY : O_WRONLY) | O_DIRECT |
                        O_CLOEXEC);
                if (-1 == fds[1]) {
                    throw std::system_error(errno, std::system_category());
                }
            }
            else {
                fds[0] = fds[1] = chunkinfo.device.cached_readwritefd_;
            }
        }
        ret = std::shared_ptr<seq_chunk>(new seq_chunk(
            chunkinfo.device,
            fds[0],
            fds[1],
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
        throw std::runtime_error("zonefs support isn't implemented yet");
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
