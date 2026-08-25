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
#include <bit>
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
#include <optional>
#include <span>
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

storage_pool::device_info_ storage_pool::read_device_identity_(
    int const fd, std::filesystem::path const &source)
{
    struct stat stat;
    memset(&stat, 0, sizeof(stat));
    MONAD_ASSERT_PRINTF(
        -1 != ::fstat(fd, &stat),
        "fstat failed due to %s",
        std::strerror(errno));
    device_info_ ret{};
    uint64_t dev_no = 0;
    uint64_t rdev = 0;
    if ((stat.st_mode & S_IFMT) == S_IFBLK) {
        ret.type = device_t::type_t_::block_device;
        MONAD_ASSERT_PRINTF(
            !ioctl(fd, _IOR(0x12, 114, size_t) /*BLKGETSIZE64*/, &ret.size),
            "ioctl failed due to %s",
            std::strerror(errno));
        rdev = static_cast<uint64_t>(stat.st_rdev);
        unsigned int logical_block_size = 0;
        // Asserted, not tolerated: absent would read as "not a block device"
        // at the addressability check, so a failure here would let a 4Kn
        // device join a database that requires 512 byte addressing.
        MONAD_ASSERT_PRINTF(
            0 == ioctl(fd, _IO(0x12, 104) /*BLKSSZGET*/, &logical_block_size),
            "ioctl failed due to %s",
            std::strerror(errno));
        ret.logical_block_size = logical_block_size;
    }
    else if ((stat.st_mode & S_IFMT) == S_IFREG) {
        ret.type = device_t::type_t_::file;
        dev_no = stat.st_ino;
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
    ret.unique_hash = compute_unique_hash_(ret.type, dev_no, ret.size);
    ret.identity = device_identity_{
        .dev = static_cast<uint64_t>(stat.st_dev),
        .ino = static_cast<uint64_t>(stat.st_ino),
        .rdev = rdev,
        .hash_dev_no = dev_no};
    return ret;
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
    device_info_ ret = read_device_identity_(fd, source);

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

bool storage_pool::has_pool_metadata(std::filesystem::path const &source)
{
    return read_device_info_(source).pool_metadata.has_value();
}

void storage_pool::refuse_duplicate_sources_(
    std::span<std::filesystem::path const> const sources)
{
    std::vector<device_info_> identities;
    identities.reserve(sources.size());
    for (auto const &source : sources) {
        int const fd = ::open(source.c_str(), O_RDONLY | O_CLOEXEC);
        MONAD_ASSERT_PRINTF(
            fd != -1,
            "open of %s failed due to %s",
            source.string().c_str(),
            std::strerror(errno));
        auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
        identities.push_back(read_device_identity_(fd, source));
    }
    for (size_t i = 0; i < identities.size(); i++) {
        for (size_t j = i + 1; j < identities.size(); j++) {
            MONAD_ASSERT_PRINTF(
                !same_device_identity_(identities[i], identities[j]),
                "Storage pool source %s and %s name the same underlying "
                "device; each device may be given only once.",
                sources[i].string().c_str(),
                sources[j].string().c_str());
        }
    }
}

storage_pool::rescan_preview storage_pool::preview_rescan(
    std::span<std::filesystem::path const> const sources,
    std::optional<file_offset_t> const recorded_size,
    std::optional<db_metadata_budget> const &budget)
{
    MONAD_ASSERT(!sources.empty());
    refuse_duplicate_sources_(sources);
    std::vector<device_info_> infos;
    infos.reserve(sources.size());
    for (auto const &source : sources) {
        infos.push_back(read_device_info_(source));
    }
    auto const plan =
        validate_devices_to_add_(sources, infos, recorded_size, budget);
    rescan_preview ret{};
    ret.existing = plan.members;
    ret.first_initialised = plan.members;
    if (plan.grown.has_value()) {
        ret.grown_previous_size = plan.grown->previous_size;
        ret.grown_previous_chunks = plan.grown->previous_chunks;
        ret.first_initialised = plan.grown->index + 1;
    }
    return ret;
}

uint32_t
storage_pool::compute_config_hash_(std::span<device_info_ const> const devices)
{
    auto hash = fnv1a_hash<uint32_t>::begin();
    for (auto const &device : devices) {
        fnv1a_hash<uint32_t>::add(hash, uint32_t(device.unique_hash));
        fnv1a_hash<uint32_t>::add(hash, uint32_t(device.unique_hash >> 32));
    }
    for (auto const &device : devices) {
        auto const &metadata = device.pool_metadata.value();
        fnv1a_hash<uint32_t>::add(hash, static_cast<uint32_t>(metadata.chunks));
        fnv1a_hash<uint32_t>::add(hash, metadata.chunk_capacity);
    }
    return uint32_t(hash);
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
    // A live device always carries its footer; only the path it was opened
    // from is no longer available.
    ret.pool_metadata = device_pool_metadata_{
        .chunk_capacity = device.metadata_->chunk_capacity,
        .num_cnv_chunks = static_cast<uint32_t>(device.cnv_chunks()),
        .config_hash = device.metadata_->config_hash,
        .chunks = device.chunks()};
    return ret;
}

bool storage_pool::same_device_identity_(
    device_info_ const &a, device_info_ const &b)
{
    MONAD_ASSERT(a.identity.has_value() && b.identity.has_value());
    auto const &x = *a.identity;
    auto const &y = *b.identity;
    if (x.dev == y.dev && x.ino == y.ino) {
        return true;
    }
    // Two distinct special files can still name the same underlying block
    // device.
    return a.type == device_t::type_t_::block_device &&
           b.type == device_t::type_t_::block_device && x.rdev == y.rdev;
}

// A device grown in place after joining a pool (LVM extend, or a backing
// file resized larger) strands its footer mid-device, so read_device_info_
// finds no MND0 at the new end and cannot tell it from a blank device. Chunks
// are written append-only from their own offset 0, so a chunk holding any data
// always has a non-zero first page; checking every chunk's first page, rather
// than trusting the absent footer, is what separates the two.
static bool device_is_blank(
    std::filesystem::path const &source, uint32_t const chunk_capacity,
    size_t const chunks)
{
    int const fd = ::open(source.c_str(), O_RDONLY | O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1,
        "open of %s failed due to %s",
        source.string().c_str(),
        std::strerror(errno));
    auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    auto *const buffer = reinterpret_cast<std::byte *>(
        aligned_alloc(DISK_PAGE_SIZE, CPU_PAGE_SIZE));
    MONAD_ASSERT(buffer != nullptr);
    auto const unbuffer = make_scope_exit([&]() noexcept { ::free(buffer); });
    for (size_t i = 0; i < chunks; i++) {
        auto const offset = file_offset_t(i) * chunk_capacity;
        auto const bytesread =
            ::pread(fd, buffer, CPU_PAGE_SIZE, static_cast<off_t>(offset));
        MONAD_ASSERT_PRINTF(
            bytesread != -1, "pread failed due to %s", std::strerror(errno));
        // A short read must never be treated as a blank page: this cannot
        // happen for a real device, since chunks is derived from the
        // device's own size, so every probed offset is well inside it.
        MONAD_ASSERT_PRINTF(
            bytesread == CPU_PAGE_SIZE,
            "Storage pool source %s could not be fully read at offset %llu "
            "while checking it is blank; refusing to treat it as blank.",
            source.string().c_str(),
            static_cast<unsigned long long>(offset));
        if (!std::all_of(buffer, buffer + bytesread, [](std::byte const b) {
                return b == std::byte{0};
            })) {
            return false;
        }
    }
    return true;
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
    ret.unique_hash = compute_unique_hash_(
        now.type, now.identity.value().hash_dev_no, grown.previous_size);
    return ret;
}

auto storage_pool::validate_grown_device_(
    std::filesystem::path const &source, device_info_ const &current,
    std::span<device_info_ const> const members,
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
    if (!members.empty()) {
        auto const &first = members[0].pool_metadata.value();
        if (capacity != first.chunk_capacity ||
            cnv_chunks != first.num_cnv_chunks) {
            return std::nullopt;
        }
    }
    auto const previous_chunks = footer->chunks(*recorded_size);
    if (previous_chunks < cnv_chunks + 1u) {
        return std::nullopt;
    }
    grown_device_ const candidate{
        .index = members.size(),
        .previous_size = *recorded_size,
        .previous_chunks = previous_chunks,
        .chunk_capacity = capacity,
        .num_cnv_chunks = cnv_chunks};
    // The recorded size implies a whole pre-grow device set, and the hash that
    // set must produce is the one the stranded footer itself stores.
    // unique_hash folds each device's size, so the recomputed hash depends on
    // the recorded size to the byte: this pins the previous size rather than
    // merely narrowing it, and four bytes spelling MND0 in trie data cannot
    // pass it. The footer predates the grow and this operation never rewrites
    // it, so it stays a fixed point to check against even across an
    // interrupted run.
    std::vector<device_info_> before(members.begin(), members.end());
    before.push_back(device_info_at_previous_size_(current, candidate));
    if (compute_config_hash_(before) != footer->config_hash) {
        return std::nullopt;
    }
    return candidate;
}

auto storage_pool::validate_devices_to_add_(
    std::span<std::filesystem::path const> const sources,
    std::span<device_info_ const> const infos,
    std::optional<file_offset_t> const recorded_size,
    std::optional<db_metadata_budget> const &budget) -> add_devices_plan_
{
    MONAD_ASSERT(sources.size() == infos.size());
    size_t prefix = 0;
    while (prefix < infos.size() && infos[prefix].pool_metadata.has_value()) {
        prefix++;
    }

    // A device extended in place presents no footer at its new end, so the
    // footer test alone cannot tell it from a blank one, and it can only sit
    // where the first footerless source does. Telling the two apart costs
    // I/O, so it waits until every arithmetic check below has had its chance
    // to refuse the set for free -- except when device 0 is itself the
    // footerless source, since then nothing else knows the pool's geometry and
    // none of those checks can run at all.
    std::optional<grown_device_> grown;
    bool tail_probed_blank = false;
    auto const classify_tail = [&] {
        // The recorded size settles the tail for one 64 byte read, where the
        // blankness probe below costs a page per chunk, so it goes first. It
        // also decides the one case the probe cannot: a device the pool already
        // owns can be empty as well as extended, since new chunks splice onto
        // the tail of the free list and one added recently stays cold for a
        // long time, and every chunk on it then reads as blank exactly like a
        // device being joined.
        bool footer_at_recorded_size = false;
        grown = validate_grown_device_(
            sources[prefix],
            infos[prefix],
            infos.subspan(0, prefix),
            recorded_size,
            footer_at_recorded_size);
        if (grown.has_value()) {
            return;
        }
        device_t::metadata_t probe{};
        // A grown device carries its own geometry in the footer the extend
        // stranded, so the probe only needs a stride to sample chunk starts
        // with. The pool's capacity is that stride whenever it is known; when
        // device 0 is itself the footerless source nothing knows it yet, and
        // the smallest capacity a pool can have divides every real one, so it
        // steps over no chunk that holds data.
        probe.chunk_capacity = infos[0].pool_metadata.has_value()
                                   ? infos[0].pool_metadata->chunk_capacity
                                   : min_chunk_capacity;
        tail_probed_blank = device_is_blank(
            sources[prefix],
            probe.chunk_capacity,
            probe.chunks(infos[prefix].size));
        if (tail_probed_blank) {
            // Reading as blank is not enough to initialise it: a footer at the
            // recorded size means this database has owned this device, so
            // whatever stopped that footer validating, joining it as new would
            // destroy the bytes-used array stranded with it.
            MONAD_ASSERT_PRINTF(
                !footer_at_recorded_size,
                "Storage pool source %s reads as blank, but pool metadata is "
                "stranded at the %llu bytes the database recorded for it and "
                "does not describe this pool. This database has owned this "
                "device, so it will not be re-initialised as a new one. "
                "Restore the device the database was last opened with, or "
                "clear this one (with blkdiscard, for example) to offer it as "
                "a genuinely new device.",
                sources[prefix].string().c_str(),
                static_cast<unsigned long long>(*recorded_size));
            return;
        }
        // A device with data but no footer at its end was extended in place.
        // Deciding that here keeps the diagnosis right: the recorded size
        // fails against a pre-grow set which is not the one the operator
        // described, so reporting that failure would name a foreign device
        // rather than a misplaced one.
        for (size_t n = prefix + 1; n < infos.size(); n++) {
            MONAD_ASSERT_PRINTF(
                !infos[n].pool_metadata.has_value(),
                "Storage pool source %s is not blank and carries no pool "
                "metadata at its end, so it was extended in place, but %s "
                "after it still belongs to the pool. Only the last device the "
                "pool already owns may be extended: growing an earlier one "
                "renumbers every chunk on the devices behind it.",
                sources[prefix].string().c_str(),
                sources[n].string().c_str());
        }
        MONAD_ASSERT_PRINTF(
            recorded_size.has_value(),
            "Storage pool source %s is not blank and carries no pool metadata "
            "at its end. If it was extended in place, the database holds no "
            "record of the size it had beforehand, which is the only thing "
            "that can locate the metadata the extend stranded; that size is "
            "recorded on every writable open, so a database last written by a "
            "release which did not record it must be opened writable once "
            "before its devices are extended. Return the device to its former "
            "size to reopen the database, or restore from a monad-mpt "
            "--archive. If the device is instead meant to join as a new one, "
            "clear it first (with blkdiscard, for example).",
            sources[prefix].string().c_str());
        MONAD_ASSERT_PRINTF(
            !footer_at_recorded_size,
            "Storage pool source %s was extended in place from the %llu bytes "
            "the database recorded for it, but the pool metadata stranded "
            "there describes a different pool, so this is not the device the "
            "database was last opened with. Restore the original device, or "
            "clear this one (with blkdiscard, for example) to offer it as a "
            "new device.",
            sources[prefix].string().c_str(),
            static_cast<unsigned long long>(*recorded_size));
        MONAD_ABORT_PRINTF(
            "Storage pool source %s is not blank and carries no pool metadata "
            "at its end, nor any at the %llu bytes the database recorded for "
            "it. If it was extended in place, it is not the device the "
            "database was last opened with; if it is meant to join as a new "
            "device, clear it first (with blkdiscard, for example).",
            sources[prefix].string().c_str(),
            static_cast<unsigned long long>(*recorded_size));
    };
    if (prefix == 0) {
        classify_tail();
        MONAD_ASSERT_PRINTF(
            grown.has_value(),
            "Storage pool source %s carries no pool metadata, so it cannot be "
            "the first source of an existing pool. The first source holds the "
            "database metadata and must be one the pool was created with.",
            sources[0].string().c_str());
    }

    uint32_t const chunk_capacity = infos[0].pool_metadata.has_value()
                                        ? infos[0].pool_metadata->chunk_capacity
                                        : grown->chunk_capacity;
    uint32_t const cnv_chunks = infos[0].pool_metadata.has_value()
                                    ? infos[0].pool_metadata->num_cnv_chunks
                                    : grown->num_cnv_chunks;
    MONAD_ASSERT_PRINTF(
        chunk_capacity != 0 && (chunk_capacity & (chunk_capacity - 1)) == 0,
        "Storage pool source %s stores chunk capacity %u, which is not a "
        "power of two, so its pool metadata is corrupt.",
        sources[0].string().c_str(),
        chunk_capacity);

    // Each source as it will be once make_device_ has carved the joining ones
    // at the pool's geometry and the grown one has taken its new size, which
    // is what the pool's new config_hash covers. Both are counted the same
    // way, so this does not depend on the classification above.
    std::vector<device_info_> joined(infos.begin(), infos.end());
    size_t total_seq_chunks = 0;
    for (size_t n = 0; n < joined.size(); n++) {
        if (n >= prefix) {
            device_t::metadata_t probe{};
            probe.chunk_capacity = chunk_capacity;
            joined[n].pool_metadata = device_pool_metadata_{
                .chunk_capacity = chunk_capacity,
                .num_cnv_chunks = cnv_chunks,
                .config_hash = 0,
                .chunks = probe.chunks(infos[n].size)};
            MONAD_ASSERT_PRINTF(
                joined[n].pool_metadata->chunks >= cnv_chunks + 1,
                "Storage pool source %s would have only %zu chunks once joined "
                "at the pool's chunk capacity; the minimum allowed is %u. Use "
                "a larger device.",
                sources[n].string().c_str(),
                joined[n].pool_metadata->chunks,
                cnv_chunks + 1);
        }
        else {
            MONAD_ASSERT_PRINTF(
                joined[n].pool_metadata->chunks >= cnv_chunks + 1,
                "Storage pool source %s has only %zu chunks, fewer than the "
                "%u this pool needs per device (%u conventional plus at least "
                "one sequential), so its pool metadata is corrupt.",
                sources[n].string().c_str(),
                joined[n].pool_metadata->chunks,
                cnv_chunks + 1,
                cnv_chunks);
        }
        total_seq_chunks += joined[n].pool_metadata->chunks - cnv_chunks;
    }

    // Both budgets are checked here so an over-large device set is refused
    // before a footer is written; the layer that owns the metadata layout
    // cannot do it for itself, because by the time it opens the footers are
    // already committed.
    //
    // chunk_info_count is a 20 bit field, and its top value is the sentinel
    // the database's free list terminates on, so a count of 0x100000 would
    // both overflow the field and produce an id indistinguishable from an
    // absent link.
    MONAD_ASSERT_PRINTF(
        total_seq_chunks <= chunk_offset_t::max_id,
        "Adding these devices would give the pool %zu sequential chunks, "
        "beyond the %llu the 20 bit chunk id space allows. Use fewer or "
        "smaller devices.",
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
        "Adding these devices would give the pool %zu sequential chunks, "
        "needing %zu bytes of database metadata, but conventional chunk 0 on "
        "%s only provides %zu. This pool's chunk capacity is too small to "
        "describe that many chunks; use fewer or smaller devices.",
        total_seq_chunks,
        metadata_bytes_needed,
        sources[0].string().c_str(),
        metadata_bytes_available);

    // The set this operation produces, and so the hash every device ends up
    // carrying. It does not depend on how the tail source is classified: a
    // grown device and a joining one are both carved at the pool's geometry
    // and both hash at their current size.
    uint32_t const target_hash = compute_config_hash_(joined);

    if (prefix > 0 && prefix < infos.size()) {
        classify_tail();
    }
    size_t const joining = prefix + (grown.has_value() ? 1 : 0);

    for (size_t n = joining; n < infos.size(); n++) {
        MONAD_ASSERT_PRINTF(
            !infos[n].pool_metadata.has_value(),
            "Storage pool source %s already carries storage pool metadata but "
            "follows source %s, which does not. Devices being added must come "
            "last and must be blank: clear the final 4Kb of %s (with "
            "blkdiscard, for example) before adding it.",
            sources[n].string().c_str(),
            sources[prefix].string().c_str(),
            sources[n].string().c_str());
        // The one moment a joining device's addressability can be checked;
        // update_aux.cpp only ever reads the ioctls from device 0. A device
        // which grew was already a member, so it is not re-checked: its
        // block size changing under the pool is out of scope.
        MONAD_ASSERT_PRINTF(
            !infos[n].logical_block_size.has_value() ||
                *infos[n].logical_block_size == 512,
            "Storage pool source %s is addressable in %u byte units, but this "
            "database requires 512 byte addressable storage.",
            sources[n].string().c_str(),
            infos[n].logical_block_size.value_or(0));
    }

    // The relocation writes the grown device's new metadata region before the
    // old one is superseded, so the two must not overlap: writing the new
    // bytes-used array over the old one would destroy the only record of how
    // full each existing chunk is while the new footer is not yet durable.
    // Refusing a growth too small to clear the old region turns that crash
    // window into an input check, and rejects nothing useful, since a growth
    // that small yields no new chunks anyway.
    if (grown.has_value()) {
        auto const &g = *grown;
        size_t const region =
            sizeof(device_t::metadata_t) +
            joined[g.index].pool_metadata->chunks * sizeof(uint32_t);
        MONAD_ASSERT_PRINTF(
            infos[g.index].size >= g.previous_size + region,
            "Storage pool source %s grew from %llu to %llu bytes, but its new "
            "metadata occupies %zu bytes and would overwrite the metadata "
            "being recovered. Extend it by at least %llu more bytes and "
            "re-run.",
            sources[g.index].string().c_str(),
            static_cast<unsigned long long>(g.previous_size),
            static_cast<unsigned long long>(infos[g.index].size),
            region,
            static_cast<unsigned long long>(
                g.previous_size + region - infos[g.index].size));
    }

    // A source storing the hash of the *whole* set is one an earlier
    // interrupted run already joined, so accepting it makes re-running the
    // same list finish an add interrupted after the footers were stamped.
    // Where a device grew, the relocation stamps that same hash on the intact
    // members before it commits, so a member carrying it may equally be a
    // grow interrupted before its own commit; either way re-running is the
    // recovery. The hash proves membership of a set with this geometry, not
    // identity: unique_hash folds a literal zero for a block device's device
    // number, so same-sized block devices are indistinguishable to it.
    std::vector<device_info_> before(
        infos.begin(), infos.begin() + static_cast<ptrdiff_t>(prefix));
    if (grown.has_value()) {
        before.push_back(
            device_info_at_previous_size_(infos[grown->index], *grown));
    }
    uint32_t const prefix_hash = compute_config_hash_(before);
    for (size_t n = 0; n < prefix; n++) {
        MONAD_ASSERT_PRINTF(
            infos[n].pool_metadata->config_hash != 0,
            "Storage pool source %s carries a pool footer but no pool identity "
            "(config hash zero), so an earlier operation initialised it and "
            "stopped before joining it to a pool. If it is one of the devices "
            "being added, clear its final 4Kb (with blkdiscard, for example) "
            "and re-run the same command.",
            sources[n].string().c_str());
        MONAD_ASSERT_PRINTF(
            infos[n].pool_metadata->config_hash == prefix_hash ||
                infos[n].pool_metadata->config_hash == target_hash,
            "Storage pool source %s stores config hash %u, which is neither "
            "the hash of the sources listed as already belonging to the pool "
            "(%u) nor the hash of the pool this operation would produce (%u). "
            "The existing sources must be listed first, in the exact order the "
            "pool was created with, followed by the sources being added. A "
            "source which belongs to a different pool must have its final 4Kb "
            "cleared (with blkdiscard, for example) before it can be added to "
            "this one.",
            sources[n].string().c_str(),
            infos[n].pool_metadata->config_hash,
            prefix_hash,
            target_hash);
        MONAD_ASSERT_PRINTF(
            infos[n].pool_metadata->chunk_capacity == chunk_capacity,
            "Storage pool source %s has chunk capacity %u but source %s has "
            "%u; the pool is inconsistent.",
            sources[n].string().c_str(),
            infos[n].pool_metadata->chunk_capacity,
            sources[0].string().c_str(),
            chunk_capacity);
    }

    // Last, because it is the only remaining check that costs real I/O: every
    // cheaper arithmetic check above has already had the chance to refuse
    // this device set first. The source classify_tail already probed is not
    // probed again.
    for (size_t n = joining; n < joined.size(); n++) {
        if (n == prefix && tail_probed_blank) {
            continue;
        }
        MONAD_ASSERT_PRINTF(
            device_is_blank(
                sources[n], chunk_capacity, joined[n].pool_metadata->chunks),
            "Storage pool source %s is not blank. It may already have been "
            "part of a storage pool, or it may have been resized in place so "
            "its pool metadata no longer sits at the end of the device. If "
            "you are certain you want to use it, clear it first (with "
            "blkdiscard, for example).",
            sources[n].string().c_str());
    }
    return add_devices_plan_{
        .members = prefix,
        .grown = grown,
        .target_hash = target_hash,
        .chunk_capacity = chunk_capacity,
        .num_cnv_chunks = cnv_chunks};
}

void storage_pool::stamp_config_hash_(
    std::filesystem::path const &source, file_offset_t const size,
    uint32_t const hash)
{
    int const fd = ::open(source.c_str(), O_RDWR | O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1,
        "open of %s failed due to %s",
        source.string().c_str(),
        std::strerror(errno));
    auto const unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    auto footer = read_footer_for_size_(fd, size);
    MONAD_ASSERT_PRINTF(
        footer.has_value(),
        "Storage pool source %s no longer carries a pool footer",
        source.string().c_str());
    if (footer->config_hash == hash) {
        // The read came through the page cache, so a match is not proof of
        // durability -- and making the members durable before the grown
        // device's footer commits is this function's whole purpose.
        MONAD_ASSERT_PRINTF(
            0 == ::fdatasync(fd),
            "fdatasync failed due to %s",
            std::strerror(errno));
        return;
    }
    footer->config_hash = hash;
    MONAD_ASSERT_PRINTF(
        ::pwrite(
            fd,
            &*footer,
            sizeof(*footer),
            static_cast<off_t>(size - sizeof(*footer))) ==
            ssize_t(sizeof(*footer)),
        "pwrite failed due to %s",
        std::strerror(errno));
    MONAD_ASSERT_PRINTF(
        0 == ::fdatasync(fd),
        "fdatasync failed due to %s",
        std::strerror(errno));
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
    // so a larger chunk count shifts every existing entry as well as the
    // array as a whole. It is therefore rebuilt and written whole; a
    // byte-for-byte copy of the old region would land every entry at the
    // wrong index.
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

void storage_pool::device_t::flush_metadata_() const
{
    auto const mapping = metadata_mapping_();
    MONAD_ASSERT_PRINTF(
        0 == ::msync(mapping.first, mapping.second, MS_SYNC),
        "msync failed due to %s",
        std::strerror(errno));
    // msync covers the mapped stores; the fd also carries the footer written
    // before the mapping existed, and any file size change made to initialise
    // the device.
    MONAD_ASSERT_PRINTF(
        0 == ::fdatasync(readwritefd_),
        "fdatasync failed due to %s",
        std::strerror(errno));
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

std::pair<int, file_offset_t> storage_pool::chunk_t::write_fd(
    size_t const bytes_which_shall_be_written) noexcept
{
    if (device().is_file() || device().is_block_device()) {
        if (!append_only_) {
            return std::pair<int, file_offset_t>{write_fd_, offset_};
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
                      write_fd_,
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
        metadata,
        freshly_initialised);
}

void storage_pool::fill_chunks_(mode const op, creation_flags const &flags)
{
    std::vector<device_info_> infos;
    infos.reserve(devices_.size());
    for (auto const &device : devices_) {
        infos.push_back(device_info_of_(device));
    }
    uint32_t const hashshouldbe = compute_config_hash_(infos);
    uint32_t const cnv_chunks_count =
        static_cast<uint32_t>(devices_[0].cnv_chunks());
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
        }
        else {
            MONAD_ABORT("zonefs support isn't implemented yet");
        }
    }
    for (auto const &device : devices_) {
        if (op == mode::add_devices) {
            // The prefix was validated against its own hash before anything
            // was written; the whole set now adopts the new hash. Devices
            // joined by an earlier interrupted run already carry it.
            device.metadata_->config_hash = hashshouldbe;
            continue;
        }
        if (device.metadata_->config_hash == 0) {
            device.metadata_->config_hash = hashshouldbe;
        }
        else if (device.metadata_->config_hash != hashshouldbe) {
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
    if (op == mode::add_devices) {
        MONAD_ASSERT(!is_read_only_);
        // The footers and their new config_hash must reach the storage before
        // DbMetadataContext makes the grown chunk_info[] durable, or a power
        // loss can leave the database describing chunks the devices do not
        // carry.
        for (auto const &device : devices_) {
            device.flush_metadata_();
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

storage_pool::storage_pool(
    storage_pool const *const src, clone_as_read_only_tag_)
    : is_read_only_(true)
    , is_read_only_allow_dirty_(false)
    , is_migration_allowed_(false)
    , is_newly_truncated_(false)
    , is_adding_devices_(false)
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
    fill_chunks_(mode::open_existing, flags);
}

storage_pool::storage_pool(
    std::span<std::filesystem::path const> const sources, mode const mode_,
    creation_flags const flags)
    : is_read_only_(flags.open_read_only || flags.open_read_only_allow_dirty)
    , is_read_only_allow_dirty_(flags.open_read_only_allow_dirty)
    , is_migration_allowed_(flags.allow_migration)
    // mode::add_devices must never set this, however much of the device set it
    // initialises: DbMetadataContext zeroes both metadata magics when it is
    // set, which would destroy the database it is meant to be growing.
    , is_newly_truncated_(mode_ == mode::truncate)
    , is_adding_devices_(mode_ == mode::add_devices)
{
    MONAD_ASSERT(!sources.empty());
    refuse_duplicate_sources_(sources);
    // Classify and validate before writing anything, the interleaving refusal
    // included. Diagnosing a bad prefix after make_device_ had already stamped
    // a footer onto the joining device would make every retry fail as "already
    // carries pool metadata", so one mistyped path would wedge the operation
    // permanently.
    size_t existing_devices = sources.size();
    add_devices_plan_ plan{};
    std::vector<device_info_> infos;
    if (mode_ == mode::add_devices) {
        MONAD_ASSERT(
            !flags.interleave_chunks_evenly,
            "Devices cannot be added to an evenly interleaved pool: chunk ids "
            "are assigned round-robin across devices, so appending a device "
            "renumbers every existing chunk.");
        MONAD_ASSERT(
            !flags.open_read_only && !flags.open_read_only_allow_dirty,
            "mode::add_devices initialises joining devices and relocates the "
            "metadata of a grown one, so it cannot be opened read only.");
        infos.reserve(sources.size());
        for (auto const &source : sources) {
            infos.push_back(read_device_info_(source));
        }
        plan = validate_devices_to_add_(
            sources,
            infos,
            flags.recorded_size_of_grown_device,
            flags.metadata_budget);
        existing_devices = plan.members;
        if (plan.grown.has_value()) {
            // Every intact member must already agree on the hash of the set
            // this operation produces before the grown device's footer lands,
            // or a crash in between would leave the grown device holding a
            // hash no other device shares and the pool unopenable. Once that
            // footer is durable the whole set agrees, which is the state the
            // append path already knows how to finish.
            for (size_t n = 0; n < plan.members; n++) {
                stamp_config_hash_(sources[n], infos[n].size, plan.target_hash);
            }
            auto const index = plan.grown->index;
            relocate_device_metadata_(
                sources[index],
                infos[index].size,
                *plan.grown,
                plan.target_hash);
            existing_devices = index + 1;
        }
    }

    devices_.reserve(sources.size());
    creation_flags device_flags = flags;
    for (size_t n = 0; n < sources.size(); n++) {
        auto const &source = sources[n];
        auto const device_mode = [&] {
            if (mode_ != mode::add_devices) {
                return mode_;
            }
            return n < existing_devices ? mode::open_existing : mode::truncate;
        }();
        if (mode_ == mode::add_devices && n == existing_devices) {
            // Joining devices take the pool's geometry, never the caller's.
            device_flags.set_chunk_capacity(
                static_cast<uint32_t>(std::countr_zero(plan.chunk_capacity)));
            device_flags.num_cnv_chunks = plan.num_cnv_chunks;
        }
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
                    device_mode,
                    device_t::type_t_::block_device,
                    source.c_str(),
                    fd,
                    0ULL,
                    device_flags);
            }
            if ((stat.st_mode & S_IFMT) == S_IFREG) {
                return make_device_(
                    device_mode,
                    device_t::type_t_::file,
                    source.c_str(),
                    fd,
                    stat.st_ino,
                    device_flags);
            }
            MONAD_ABORT_PRINTF(
                "Storage pool source %s has unknown file entry type = %u",
                source.string().c_str(),
                stat.st_mode & S_IFMT);
        }());
    }
    fill_chunks_(mode_, flags);
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
    , is_adding_devices_(false)
{
    int const fd = make_temporary_inode();
    auto unfd = make_scope_exit([fd]() noexcept { ::close(fd); });
    MONAD_ASSERT_PRINTF(
        -1 != ::ftruncate(fd, len), "failed due to %s", std::strerror(errno));
    devices_.push_back(make_device_(
        mode::truncate, device_t::type_t_::file, {}, fd, uint64_t(0), flags));
    unfd.release();
    fill_chunks_(mode::truncate, flags);
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
            auto const mapping = device.metadata_mapping_();
            ::munmap(mapping.first, mapping.second);
        }
        if (device.readwritefd_ != -1) {
            (void)::fsync(device.readwritefd_);
            (void)::close(device.readwritefd_);
        }
    }
    devices_.clear();
}

storage_pool::chunk_t &
storage_pool::chunk(chunk_type const which, uint32_t const id)
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
