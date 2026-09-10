// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/async/detail/scope_polyfill.hpp>
#include <category/core/assert.h>
#include <category/core/detail/start_lifetime_as_polyfill.hpp>
#include <category/core/log.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/db_stats_shm.hpp>
#include <category/mpt/detail/collected_stats.hpp>

#include <atomic>
#include <cerrno>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <optional>
#include <utility>

#include <fcntl.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

MONAD_MPT_NAMESPACE_BEGIN

namespace
{
    // A publish holds the seqlock only for a 160 byte copy, so losing this
    // many races in a row means racing a writer the scheduler stopped mid
    // publish. The sample is dropped and the next scrape picks it up.
    constexpr unsigned READ_ATTEMPTS = 8;

    detail::db_stats_shm *map_shm(int const fd, int const prot)
    {
        void *const addr = ::mmap(
            nullptr, sizeof(detail::db_stats_shm), prot, MAP_SHARED, fd, 0);
        if (addr == MAP_FAILED) {
            return nullptr;
        }
        return start_lifetime_as<detail::db_stats_shm>(addr);
    }

    // Whether `fd` holds a sidecar this code wrote, so that a mistyped path
    // costs the operator their metrics rather than the file they named.
    bool holds_sidecar(int const fd, off_t const size)
    {
        // Empty carries nothing to lose, and refusing it would permanently
        // strand a sidecar whose writer died before its first header write.
        if (size == 0) {
            return true;
        }
        if (std::cmp_less(size, detail::db_stats_shm::HEADER_SIZE)) {
            return false;
        }
        uint64_t magic{0};
        return ::pread(fd, &magic, sizeof(magic), 0) ==
                   static_cast<ssize_t>(sizeof(magic)) &&
               magic == detail::db_stats_shm::MAGIC;
    }
}

std::optional<DbStatsPublisher>
DbStatsPublisher::create(std::filesystem::path const &path)
{
    int fd = ::open(path.c_str(), O_RDWR | O_CREAT | O_EXCL | O_CLOEXEC, 0644);
    bool const created = fd != -1;
    if (!created) {
        if (errno != EEXIST) {
            LOG_WARNING(
                "cannot create db stats file {}: {}",
                path.string(),
                std::strerror(errno));
            return std::nullopt;
        }
        fd = ::open(path.c_str(), O_RDWR | O_CLOEXEC, 0644);
        if (fd == -1) {
            LOG_WARNING(
                "cannot open db stats file {}: {}",
                path.string(),
                std::strerror(errno));
            return std::nullopt;
        }
    }
    auto close_fd = monad::make_scope_exit([&]() noexcept { ::close(fd); });

    // The seqlock has exactly one writer. Without this, two publishers on one
    // path interleave into snapshots that pass a reader's checks while mixing
    // both processes' totals.
    if (::flock(fd, LOCK_EX | LOCK_NB) == -1) {
        LOG_ERROR(
            "cannot lock db stats file {}: {}. Another process is publishing "
            "to it",
            path.string(),
            std::strerror(errno));
        return std::nullopt;
    }

    struct ::stat st;
    if (::fstat(fd, &st) == -1) {
        LOG_WARNING(
            "cannot stat db stats file {}: {}",
            path.string(),
            std::strerror(errno));
        return std::nullopt;
    }
    if (!S_ISREG(st.st_mode) || (!created && !holds_sidecar(fd, st.st_size))) {
        LOG_ERROR(
            "{} is not a db stats file; refusing to overwrite it",
            path.string());
        return std::nullopt;
    }

    // Reserve the blocks now: ftruncate alone leaves the mapping sparse, and
    // then a full filesystem turns the first store below into a SIGBUS that
    // takes down a process that was only publishing metrics.
    if (int const rc = ::posix_fallocate(fd, 0, sizeof(detail::db_stats_shm));
        rc != 0) {
        LOG_WARNING(
            "cannot allocate db stats file {}: {}",
            path.string(),
            std::strerror(rc));
        return std::nullopt;
    }
    detail::db_stats_shm *const shm = map_shm(fd, PROT_READ | PROT_WRITE);
    if (shm == nullptr) {
        LOG_WARNING(
            "cannot map db stats file {}: {}",
            path.string(),
            std::strerror(errno));
        return std::nullopt;
    }

    std::atomic_ref<uint64_t> const magic{shm->magic};
    // Clearing the magic first is what makes it a readiness flag on the path
    // where the file already carried one: a reader arriving mid-takeover is
    // turned away instead of parsing a half-rewritten header.
    magic.store(0, std::memory_order_release);

    // Round up to odd rather than adding, so a sequence left odd by a writer
    // that died mid-publish cannot leave the lock held forever.
    std::atomic_ref<uint32_t> const seq{shm->seq};
    uint32_t const held = seq.load(std::memory_order_relaxed) | 1U;
    seq.store(held, std::memory_order_relaxed);
    std::atomic_thread_fence(std::memory_order_release);
    shm->update_stats = {};
    shm->format_version = detail::db_stats_shm::FORMAT_VERSION;
    shm->payload_size = sizeof(detail::TrieUpdateCollectedStats);
    shm->unused_ = 0;
    seq.store(held + 1, std::memory_order_release);

    magic.store(detail::db_stats_shm::MAGIC, std::memory_order_release);

    LOG_INFO("publishing db stats to {}", path.string());
    close_fd.release();
    return DbStatsPublisher{shm, fd};
}

DbStatsPublisher::DbStatsPublisher(DbStatsPublisher &&other) noexcept
    : shm_{std::exchange(other.shm_, nullptr)}
    , fd_{std::exchange(other.fd_, -1)}
{
}

DbStatsPublisher::~DbStatsPublisher()
{
    if (shm_ != nullptr) {
        ::munmap(shm_, sizeof(detail::db_stats_shm));
        shm_ = nullptr;
    }
    if (fd_ != -1) {
        ::close(fd_); // drops the flock
        fd_ = -1;
    }
}

void DbStatsPublisher::publish_update_stats(
    detail::TrieUpdateCollectedStats const &s) noexcept
{
    MONAD_DEBUG_ASSERT(shm_ != nullptr);
    std::atomic_ref<uint32_t> const seq{shm_->seq};
    uint32_t const begin = seq.load(std::memory_order_relaxed);
    seq.store(begin + 1, std::memory_order_relaxed);
    std::atomic_thread_fence(std::memory_order_release);
    shm_->update_stats = s;
    seq.store(begin + 2, std::memory_order_release);
}

std::optional<DbStatsReader>
DbStatsReader::open(std::filesystem::path const &path)
{
    int const fd = ::open(path.c_str(), O_RDONLY | O_CLOEXEC);
    if (fd == -1) {
        // A path no writer has reached yet is the ordinary case and stays
        // quiet; anything else is a deployment the operator has to fix.
        if (errno != ENOENT) {
            LOG_WARNING(
                "cannot open db stats file {}: {}",
                path.string(),
                std::strerror(errno));
        }
        return std::nullopt;
    }
    auto const close_fd =
        monad::make_scope_exit([&]() noexcept { ::close(fd); });

    struct ::stat st;
    if (::fstat(fd, &st) == -1 ||
        std::cmp_less(st.st_size, detail::db_stats_shm::HEADER_SIZE)) {
        LOG_WARNING(
            "db stats file {} is too small to hold a header", path.string());
        return std::nullopt;
    }
    // Mapping the whole struct over a shorter file is safe: the tail lands in
    // the page holding end of file, reads as zero, and payload_size reports
    // the sections that writer predates as absent.
    detail::db_stats_shm *const shm = map_shm(fd, PROT_READ);
    if (shm == nullptr) {
        LOG_WARNING(
            "cannot map db stats file {}: {}",
            path.string(),
            std::strerror(errno));
        return std::nullopt;
    }
    if (std::atomic_ref<uint64_t>{shm->magic}.load(std::memory_order_acquire) !=
        detail::db_stats_shm::MAGIC) {
        ::munmap(shm, sizeof(detail::db_stats_shm));
        return std::nullopt;
    }
    if (shm->format_version != detail::db_stats_shm::FORMAT_VERSION) {
        LOG_WARNING(
            "db stats file {} has layout version {}, this build writes {}",
            path.string(),
            shm->format_version,
            detail::db_stats_shm::FORMAT_VERSION);
        ::munmap(shm, sizeof(detail::db_stats_shm));
        return std::nullopt;
    }
    return DbStatsReader{shm};
}

DbStatsReader::DbStatsReader(DbStatsReader &&other) noexcept
    : shm_{std::exchange(other.shm_, nullptr)}
{
}

DbStatsReader::~DbStatsReader()
{
    if (shm_ != nullptr) {
        ::munmap(shm_, sizeof(detail::db_stats_shm));
        shm_ = nullptr;
    }
}

std::optional<detail::TrieUpdateCollectedStats>
DbStatsReader::read_update_stats() const noexcept
{
    MONAD_DEBUG_ASSERT(shm_ != nullptr);
    std::atomic_ref<uint32_t> const seq{shm_->seq};
    for (unsigned attempt = 0; attempt < READ_ATTEMPTS; ++attempt) {
        uint32_t const begin = seq.load(std::memory_order_acquire);
        if (begin & 1U) {
            continue;
        }
        uint32_t const payload_size = shm_->payload_size;
        detail::TrieUpdateCollectedStats stats = shm_->update_stats;
        std::atomic_thread_fence(std::memory_order_acquire);
        if (seq.load(std::memory_order_relaxed) != begin) {
            continue;
        }
        if (payload_size < sizeof(detail::TrieUpdateCollectedStats)) {
            return std::nullopt;
        }
        return stats;
    }
    return std::nullopt;
}

MONAD_MPT_NAMESPACE_END
