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
#include <optional>
#include <utility>
#include <variant>
#include <vector>

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

uint64_t storage_pool::compute_unique_hash_(
    device_t::type_t_ const type, uint64_t const dev_no,
    file_offset_t const size)
{
    auto hash = fnv1a_hash<uint32_t>::begin();
    fnv1a_hash<uint32_t>::add(hash, uint32_t(type));
    fnv1a_hash<uint32_t>::add(hash, uint32_t(dev_no));
    fnv1a_hash<uint32_t>::add(hash, uint32_t(dev_no >> 32));
    fnv1a_hash<uint32_t>::add(hash, uint32_t(size));
    return hash;
}

storage_pool::device_info_
storage_pool::read_device_info_(std::filesystem::path const &source)
{
    int const fd = ::open(source.c_str(), O_RDONLY | O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1,
        "open of %s failed due to %s",
        source.string().c_str(),
        std::strerror(errno));
    auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    struct stat stat;
    memset(&stat, 0, sizeof(stat));
    MONAD_ASSERT_PRINTF(
        -1 != ::fstat(fd, &stat),
        "fstat failed due to %s",
        std::strerror(errno));
    device_info_ ret{};
    if ((stat.st_mode & S_IFMT) == S_IFBLK) {
        ret.type = device_t::type_t_::block_device;
        MONAD_ASSERT_PRINTF(
            !ioctl(fd, _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/, &ret.size),
            "ioctl failed due to %s",
            std::strerror(errno));
        ret.hash_dev_no = 0;
    }
    else if ((stat.st_mode & S_IFMT) == S_IFREG) {
        ret.type = device_t::type_t_::file;
        ret.hash_dev_no = static_cast<uint64_t>(stat.st_ino);
        ret.size = static_cast<file_offset_t>(stat.st_size);
    }
    else {
        MONAD_ABORT_PRINTF(
            "Storage pool source %s has unknown file entry type = %u",
            source.string().c_str(),
            stat.st_mode & S_IFMT);
    }
    MONAD_ASSERT_PRINTF(
        ret.size >= CPU_PAGE_SIZE,
        "Storage pool source %s must be at least 4Kb long",
        source.string().c_str());
    ret.unique_hash = compute_unique_hash_(ret.type, ret.hash_dev_no, ret.size);

    auto *const buffer = reinterpret_cast<std::byte *>(
        aligned_alloc(DISK_PAGE_SIZE, DISK_PAGE_SIZE * 2));
    MONAD_ASSERT(buffer != nullptr);
    auto const unbuffer = make_scope_exit([&]() noexcept { ::free(buffer); });
    auto const offset = round_down_align<DISK_PAGE_BITS>(
        ret.size - sizeof(device_t::metadata_t));
    auto const bytesread = ::pread(
        fd,
        buffer,
        static_cast<size_t>(ret.size - offset),
        static_cast<off_t>(offset));
    MONAD_ASSERT_PRINTF(
        bytesread != -1, "pread failed due to %s", std::strerror(errno));
    // The footer is located from the byte count, so a short read would point
    // it at the wrong bytes -- and at zero bytes, before the buffer entirely.
    // What those bytes say is whether this device belongs to a pool.
    MONAD_ASSERT_PRINTF(
        static_cast<file_offset_t>(bytesread) == ret.size - offset,
        "read %zd of %llu bytes of %s's pool footer",
        bytesread,
        static_cast<unsigned long long>(ret.size - offset),
        source.string().c_str());
    auto const *const footer = start_lifetime_as<device_t::metadata_t>(
        buffer + bytesread - sizeof(device_t::metadata_t));
    if (memcmp(footer->magic, "MND0", 4) == 0) {
        ret.pool_metadata = device_pool_metadata_{
            .chunk_capacity = footer->chunk_capacity,
            .num_cnv_chunks = footer->num_cnv_chunks == 0
                                  ? legacy_default_num_cnv_chunks
                                  : footer->num_cnv_chunks,
            .config_hash = footer->config_hash,
            .chunks = footer->chunks(ret.size)};
    }
    return ret;
}

storage_pool::rescan_preview storage_pool::preview_rescan(
    std::filesystem::path const &source,
    std::optional<file_offset_t> const recorded_size,
    std::optional<db_metadata_budget> const &budget)
{
    auto const info = read_device_info_(source);
    rescan_preview ret{};
    if (auto const grown =
            validate_device_to_rescan_(source, info, recorded_size, budget)) {
        ret.grown_previous_size = grown->previous_size;
        ret.grown_previous_chunks = grown->previous_chunks;
    }
    return ret;
}

uint32_t storage_pool::compute_config_hash_(device_info_ const &device)
{
    auto hash = fnv1a_hash<uint32_t>::begin();
    fnv1a_hash<uint32_t>::add(hash, uint32_t(device.unique_hash));
    fnv1a_hash<uint32_t>::add(hash, uint32_t(device.unique_hash >> 32));
    auto const &metadata = device.pool_metadata.value();
    fnv1a_hash<uint32_t>::add(hash, static_cast<uint32_t>(metadata.chunks));
    fnv1a_hash<uint32_t>::add(hash, metadata.chunk_capacity);
    return uint32_t(hash);
}

auto storage_pool::read_footer_for_size_(int const fd, file_offset_t const size)
    -> std::optional<device_t::metadata_t>
{
    if (size < sizeof(device_t::metadata_t)) {
        return std::nullopt;
    }
    device_t::metadata_t footer{};
    auto const bytesread = ::pread(
        fd, &footer, sizeof(footer), static_cast<off_t>(size - sizeof(footer)));
    MONAD_ASSERT_PRINTF(
        bytesread != -1, "pread failed due to %s", std::strerror(errno));
    if (static_cast<size_t>(bytesread) != sizeof(footer) ||
        memcmp(footer.magic, "MND0", 4) != 0) {
        return std::nullopt;
    }
    return footer;
}

storage_pool::device_info_ storage_pool::device_info_at_previous_size_(
    device_info_ const &now, grown_device_ const &grown)
{
    device_info_ ret = now;
    ret.size = grown.previous_size;
    ret.pool_metadata = device_pool_metadata_{
        .chunk_capacity = grown.chunk_capacity,
        .num_cnv_chunks = grown.num_cnv_chunks,
        // The stranded footer's own config_hash is what the caller compares
        // against, so it is deliberately not carried over here.
        .config_hash = 0,
        .chunks = grown.previous_chunks};
    ret.unique_hash =
        compute_unique_hash_(now.type, now.hash_dev_no, grown.previous_size);
    return ret;
}

auto storage_pool::validate_grown_device_(
    std::filesystem::path const &source, device_info_ const &current,
    std::optional<file_offset_t> const recorded_size, bool &footer_found)
    -> std::optional<grown_device_>
{
    footer_found = false;
    if (!recorded_size.has_value() || *recorded_size >= current.size ||
        *recorded_size < CPU_PAGE_SIZE) {
        return std::nullopt;
    }
    int const fd = ::open(source.c_str(), O_RDONLY | O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1,
        "open of %s failed due to %s",
        source.string().c_str(),
        std::strerror(errno));
    auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    auto const footer = read_footer_for_size_(fd, *recorded_size);
    if (!footer.has_value()) {
        return std::nullopt;
    }
    footer_found = true;
    auto const capacity = footer->chunk_capacity;
    if (capacity == 0 || (capacity & (capacity - 1)) != 0) {
        return std::nullopt;
    }
    auto const cnv_chunks = footer->num_cnv_chunks == 0
                                ? legacy_default_num_cnv_chunks
                                : footer->num_cnv_chunks;
    auto const previous_chunks = footer->chunks(*recorded_size);
    if (previous_chunks < cnv_chunks + 1u) {
        return std::nullopt;
    }
    grown_device_ const candidate{
        .previous_size = *recorded_size,
        .previous_chunks = previous_chunks,
        .chunk_capacity = capacity,
        .num_cnv_chunks = cnv_chunks};
    // The hash the device must have produced before it grew is the one the
    // stranded footer itself stores. unique_hash folds the device's size, so
    // the recomputed hash depends on the recorded size -- through the chunk
    // count it is folded into, since the hash itself folds only its low 32
    // bits -- so this pins
    // the previous size rather than merely narrowing it, and four bytes
    // spelling MND0 in trie data cannot pass it. The footer predates the grow
    // and this operation never rewrites it, so it stays a fixed point to check
    // against even across an interrupted run.
    if (compute_config_hash_(device_info_at_previous_size_(
            current, candidate)) != footer->config_hash) {
        return std::nullopt;
    }
    return candidate;
}

auto storage_pool::validate_device_to_rescan_(
    std::filesystem::path const &source, device_info_ const &info,
    std::optional<file_offset_t> const recorded_size,
    std::optional<db_metadata_budget> const &budget)
    -> std::optional<grown_device_>
{
    std::optional<grown_device_> grown;
    if (!info.pool_metadata.has_value()) {
        // No footer at the end this size gives it, so either an extend
        // stranded it mid-device or this is not the pool's device at all.
        bool footer_at_recorded_size = false;
        grown = validate_grown_device_(
            source, info, recorded_size, footer_at_recorded_size);
        MONAD_ASSERT_PRINTF(
            recorded_size.has_value(),
            "Storage pool source %s carries no pool metadata at its end. If it "
            "was extended in place, the database holds no record of the size "
            "it had beforehand, which is the only thing that can locate the "
            "metadata the extend stranded; that size is recorded on every "
            "writable open, so a database last written by a release which did "
            "not record it must be opened writable once before its device is "
            "extended. Return the device to its former size to reopen the "
            "database, or restore from a monad-mpt --archive.",
            source.string().c_str());
        MONAD_ASSERT_PRINTF(
            !footer_at_recorded_size || grown.has_value(),
            "Storage pool source %s was extended in place from the %llu bytes "
            "the database recorded for it, but the pool metadata stranded "
            "there describes a different pool, so this is not the device the "
            "database was last opened with. Restore the original device.",
            source.string().c_str(),
            static_cast<unsigned long long>(*recorded_size));
        MONAD_ASSERT_PRINTF(
            grown.has_value(),
            "Storage pool source %s carries no pool metadata at its end, nor "
            "any at the %llu bytes the database recorded for it. If it was "
            "extended in place, it is not the device the database was last "
            "opened with.",
            source.string().c_str(),
            static_cast<unsigned long long>(*recorded_size));
    }
    else if (info.pool_metadata->config_hash != 0) {
        // The device was not extended, so the footer at its end is the one to
        // rescan against. adopt_device_ would reject a foreign one, but only
        // after the operator has confirmed: this function is what a caller
        // puts in front of that prompt, so the same refusal belongs here. A
        // zero hash is a pool which has never been adopted, which adopt_device_
        // stamps rather than refuses.
        MONAD_ASSERT_PRINTF(
            info.pool_metadata->config_hash == compute_config_hash_(info),
            "Storage pool source %s carries pool metadata at its end which was "
            "initialised with a configuration different to this storage pool, "
            "so this is not the device the database was last opened with.",
            source.string().c_str());
    }
    uint32_t const chunk_capacity = grown.has_value()
                                        ? grown->chunk_capacity
                                        : info.pool_metadata->chunk_capacity;
    uint32_t const cnv_chunks = grown.has_value()
                                    ? grown->num_cnv_chunks
                                    : info.pool_metadata->num_cnv_chunks;
    device_t::metadata_t probe{};
    probe.chunk_capacity = chunk_capacity;
    size_t const total_chunks = probe.chunks(info.size);
    MONAD_ASSERT_PRINTF(
        total_chunks > cnv_chunks,
        "Storage pool source %s offers %zu chunks, fewer than the %u "
        "conventional chunks the pool reserves.",
        source.string().c_str(),
        total_chunks,
        cnv_chunks);
    size_t const total_seq_chunks = total_chunks - cnv_chunks;

    // The relocation writes the new metadata region before the old one is
    // superseded, so the two must not overlap: writing the new bytes-used
    // array over the old one would destroy the only record of how full each
    // existing chunk is while the new footer is not yet durable. Refusing a
    // growth too small to clear the old region turns that crash window into an
    // input check, and rejects nothing useful, since a growth that small
    // yields no new chunks anyway.
    if (grown.has_value()) {
        size_t const region =
            sizeof(device_t::metadata_t) + total_chunks * sizeof(uint32_t);
        MONAD_ASSERT_PRINTF(
            info.size >= grown->previous_size + region,
            "Storage pool source %s grew from %llu to %llu bytes, but its new "
            "metadata occupies %zu bytes and would overwrite the metadata "
            "being recovered. Extend it by at least %llu more bytes and "
            "re-run.",
            source.string().c_str(),
            static_cast<unsigned long long>(grown->previous_size),
            static_cast<unsigned long long>(info.size),
            region,
            static_cast<unsigned long long>(
                grown->previous_size + region - info.size));
    }

    // Both budgets are checked here so an over-large device is refused before
    // a footer is written; the layer that owns the metadata layout cannot do
    // it for itself, because by the time it opens the footer is already
    // committed.
    //
    // chunk_info_count is a 20 bit field, and its top value is the sentinel
    // the database's free list terminates on, so a count of 0x100000 would
    // both overflow the field and produce an id indistinguishable from an
    // absent link.
    MONAD_ASSERT_PRINTF(
        total_seq_chunks <= chunk_offset_t::max_id,
        "Taking up this device would give the pool %zu sequential chunks, "
        "beyond the %llu the 20 bit chunk id space allows. Use a smaller "
        "device.",
        total_seq_chunks,
        static_cast<unsigned long long>(chunk_offset_t::max_id));
    size_t const metadata_bytes_needed =
        budget.has_value()
            ? budget->header_bytes + total_seq_chunks * budget->bytes_per_chunk
            : 0;
    size_t const metadata_bytes_available = chunk_capacity / 2;
    MONAD_ASSERT_PRINTF(
        !budget.has_value() ||
            metadata_bytes_available >= metadata_bytes_needed,
        "Taking up this device would give the pool %zu sequential chunks, "
        "needing %zu bytes of database metadata, but conventional chunk 0 on "
        "%s only provides %zu. This pool's chunk capacity is too small to "
        "describe that many chunks; use a smaller device.",
        total_seq_chunks,
        metadata_bytes_needed,
        source.string().c_str(),
        metadata_bytes_available);
    return grown;
}

void storage_pool::relocate_device_metadata_(
    std::filesystem::path const &source, file_offset_t const current_size,
    grown_device_ const &grown, uint32_t const new_config_hash)
{
    int const fd = ::open(source.c_str(), O_RDWR | O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1,
        "open of %s failed due to %s",
        source.string().c_str(),
        std::strerror(errno));
    auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });

    device_t::metadata_t footer{};
    footer.chunk_capacity = grown.chunk_capacity;
    footer.num_cnv_chunks = grown.num_cnv_chunks;
    footer.config_hash = new_config_hash;
    // chunks() carries a correction which drops the last chunk when the
    // metadata region would otherwise collide with it, so it must be called
    // rather than reimplemented.
    auto const new_chunks = footer.chunks(current_size);
    MONAD_ASSERT(new_chunks >= grown.previous_chunks);
    auto const array_bytes = new_chunks * sizeof(uint32_t);
    auto const array_base = current_size - sizeof(footer) - array_bytes;
    MONAD_ASSERT(array_base >= grown.previous_size);

    // The array is anchored to the footer and indexed upward from its base,
    // so a larger chunk count moves it bodily downward while entry n keeps
    // index n. Written whole rather than copied so that the entries the
    // extend uncovered are zeroed instead of holding the old region's bytes.
    std::vector<uint32_t> bytes_used(new_chunks, 0);
    auto const old_array_bytes = grown.previous_chunks * sizeof(uint32_t);
    auto const old_array_base =
        grown.previous_size - sizeof(footer) - old_array_bytes;
    auto const bytesread = ::pread(
        fd,
        bytes_used.data(),
        old_array_bytes,
        static_cast<off_t>(old_array_base));
    MONAD_ASSERT_PRINTF(
        bytesread != -1, "pread failed due to %s", std::strerror(errno));
    MONAD_ASSERT_PRINTF(
        static_cast<size_t>(bytesread) == old_array_bytes,
        "read %zd of %zu bytes of the stranded per-chunk bytes-used array "
        "on %s",
        bytesread,
        old_array_bytes,
        source.string().c_str());

    MONAD_ASSERT_PRINTF(
        ::pwrite(
            fd,
            bytes_used.data(),
            array_bytes,
            static_cast<off_t>(array_base)) == ssize_t(array_bytes),
        "pwrite failed due to %s",
        std::strerror(errno));
    MONAD_ASSERT_PRINTF(
        0 == ::fdatasync(fd),
        "fdatasync failed due to %s",
        std::strerror(errno));

    // The footer at the new end is what makes the device valid, so it commits
    // the relocation. A crash before it is durable leaves the device still
    // classified as grown, and re-running simply redoes the whole operation.
    memcpy(footer.magic, "MND0", sizeof(footer.magic));
    MONAD_ASSERT_PRINTF(
        ::pwrite(
            fd,
            &footer,
            sizeof(footer),
            static_cast<off_t>(current_size - sizeof(footer))) ==
            ssize_t(sizeof(footer)),
        "pwrite failed due to %s",
        std::strerror(errno));
    MONAD_ASSERT_PRINTF(
        0 == ::fdatasync(fd),
        "fdatasync failed due to %s",
        std::strerror(errno));
}

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

std::pair<void *, size_t>
storage_pool::device_t::metadata_mapping_() const noexcept
{
    auto const total_size = metadata_->total_size(size_of_file_);
    auto const offset =
        round_down_align<CPU_PAGE_BITS>(size_of_file_ - total_size);
    auto const mapped_bytes =
        round_up_align<CPU_PAGE_BITS>(size_of_file_ - offset);
    auto const metadata_from_base =
        static_cast<size_t>(size_of_file_ - offset) - sizeof(metadata_t);
    return {
        reinterpret_cast<std::byte *>(metadata_) - metadata_from_base,
        static_cast<size_t>(mapped_bytes)};
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
    uint64_t unique_hash = 0;
    auto const *const dev_no = std::get_if<0>(&dev_no_or_dev);
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
    if (dev_no != nullptr) {
        unique_hash = compute_unique_hash_(
            type, *dev_no, static_cast<file_offset_t>(stat.st_size));
    }
    size_t total_size = 0;
    bool freshly_initialised = false;
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
            freshly_initialised = true;
            // Uninitialised
            if (op == mode::open_existing) {
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s has not been initialised for use "
                    "with storage pool. A device extended in place also "
                    "presents this way, because the pool metadata is still at "
                    "the size the device had before: run monad-mpt "
                    "--rescan-devices on it to take up the new space.",
                    path.string().c_str());
            }
            if (op == mode::rescan) {
                // A rescan has either just relocated the footer to this
                // device's end or found one already there, so reaching this
                // means the device is not the one that was validated. Falling
                // through would discard the database.
                MONAD_ABORT_PRINTF(
                    "Storage pool source %s carries no pool metadata at its "
                    "end, so it is not the device the rescan validated",
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
        metadata,
        freshly_initialised);
}

storage_pool::device_info_ storage_pool::device_info_of_(device_t const &device)
{
    MONAD_ASSERT(
        device.is_file() || device.is_block_device(),
        "zonefs support isn't implemented yet");
    device_info_ ret{};
    ret.type = device.type_;
    ret.unique_hash = device.unique_hash_;
    ret.size = device.size_of_file_;
    // A live device always carries its footer.
    ret.pool_metadata = device_pool_metadata_{
        .chunk_capacity = device.metadata_->chunk_capacity,
        .num_cnv_chunks = static_cast<uint32_t>(device.cnv_chunks()),
        .config_hash = device.metadata_->config_hash,
        .chunks = device.chunks()};
    return ret;
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

    // A rescan needs no case of its own: relocate_device_metadata_ wrote the
    // footer at the device's new end carrying the hash this recomputes, so the
    // ordinary check passes.
    uint32_t const hashshouldbe =
        compute_config_hash_(device_info_of_(device_));
    if (device_.metadata_->config_hash == 0) {
        device_.metadata_->config_hash = hashshouldbe;
    }
    else if (device_.metadata_->config_hash != hashshouldbe) {
        if (!flags.disable_mismatching_storage_pool_check) {
            MONAD_ABORT_PRINTF(
                "Storage pool source %s was initialised with a configuration "
                "different to this storage pool. Was it resized without "
                "running monad-mpt --rescan-devices?\n\nYou should use the "
                "monad-mpt tool to copy and move databases around, NOT by "
                "copying partition contents!",
                device_.current_path().c_str());
        }
        else {
            MONAD_ABORT_PRINTF(
                "Storage pool source %s was initialised with a configuration "
                "different to this storage pool. Was it resized without "
                "running monad-mpt --rescan-devices?\n\nYou should use the "
                "monad-mpt tool to copy and move databases around, NOT by "
                "copying partition contents!\n\nSince the monad-mpt tool was "
                "added, the flag disable_mismatching_storage_pool_check is no "
                "longer needed and has been disabled.",
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
    // A grown device has no footer at the end its new size gives it, so the
    // metadata has to be moved there before the device can be opened at all.
    // Everything this needs is validated first, so a refused device is left
    // untouched.
    if (op == mode::rescan) {
        MONAD_ASSERT(
            !flags.open_read_only && !flags.open_read_only_allow_dirty,
            "mode::rescan relocates the metadata of a grown device, so it "
            "cannot be opened read only.");
        // Without the budget, the only refusal that catches a device too large
        // for the database's metadata comes after the footer has been
        // relocated, which leaves the pool unopenable at any size but the one
        // it had before.
        MONAD_ASSERT(
            flags.metadata_budget.has_value(),
            "mode::rescan needs the owning layer's metadata budget to refuse "
            "an over-large device before committing the relocation.");
        auto const info = read_device_info_(source);
        if (auto const grown = validate_device_to_rescan_(
                source,
                info,
                flags.recorded_size_of_grown_device,
                flags.metadata_budget)) {
            device_t::metadata_t probe{};
            probe.chunk_capacity = grown->chunk_capacity;
            device_info_ after = info;
            after.pool_metadata = device_pool_metadata_{
                .chunk_capacity = grown->chunk_capacity,
                .num_cnv_chunks = grown->num_cnv_chunks,
                .config_hash = 0,
                .chunks = probe.chunks(info.size)};
            // The relocated footer is the commit record, and with one device
            // it is the only one: no sibling has to carry the new hash first.
            relocate_device_metadata_(
                source, info.size, *grown, compute_config_hash_(after));
        }
    }
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
    , is_rescanning_(false)
    , device_(reopen_device_read_only_(src->device_))
{
    creation_flags flags;
    flags.open_read_only = true;
    adopt_device_(flags);
}

storage_pool::storage_pool(
    std::filesystem::path const &source, mode const mode_,
    creation_flags const flags)
    : is_read_only_(flags.open_read_only || flags.open_read_only_allow_dirty)
    , is_read_only_allow_dirty_(flags.open_read_only_allow_dirty)
    , is_migration_allowed_(flags.allow_migration)
    // mode::rescan must never set this: DbMetadataContext zeroes both
    // metadata magics when it is set, which would destroy the database it is
    // meant to be growing.
    , is_newly_truncated_(mode_ == mode::truncate)
    , is_rescanning_(mode_ == mode::rescan)
    , device_(open_device_(source, mode_, flags))
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
    , is_rescanning_(false)
    , device_(make_anonymous_device_(len, flags))
{
    adopt_device_(flags);
}

storage_pool::~storage_pool()
{
    if (device_.metadata_ != nullptr) {
        auto const mapping = device_.metadata_mapping_();
        ::munmap(mapping.first, mapping.second);
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
