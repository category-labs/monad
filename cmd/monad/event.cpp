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

#include "event.hpp"

#include <category/core/cleanup.h>
#include <category/core/config.hpp>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>

#include <charconv>
#include <concepts>
#include <csignal>
#include <cstdint>
#include <cstring>
#include <expected>
#include <format>
#include <memory>
#include <optional>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <utility>
#include <vector>

#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <unistd.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

template <std::integral I>
std::string try_parse_int_token(std::string_view s, I *i)
{
    std::from_chars_result const r = std::from_chars(begin(s), end(s), *i, 10);
    if (r.ptr != data(s) + size(s)) {
        return std::format("{} contains non-integer characters", s);
    }
    if (static_cast<int>(r.ec) != 0) {
        std::error_condition const e{r.ec};
        return std::format(
            "could not parse {} as integer: {} ({})",
            s,
            e.message(),
            e.value());
    }
    return {};
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

// Parse a configuration string, which has the form
//
//   <ring-name-or-path>[:<descriptor-shift>:<buf-shift>]
//
// A shift can be empty, e.g., <descriptor-shift> in `my-file::30`, in which
// case the default value is used
std::expected<EventRingConfig, std::string>
try_parse_event_ring_config(std::string_view s)
{
    std::vector<std::string_view> tokens;
    EventRingConfig cfg;

    for (auto t : std::views::split(s, ':')) {
        tokens.emplace_back(t);
    }

    if (size(tokens) < 1 || size(tokens) > 3) {
        return std::unexpected(std::format(
            "input `{}` does not have "
            "expected format "
            "<ring-name-or-path>[:<descriptor-shift>:<payload-buffer-shift>]",
            s));
    }
    cfg.event_ring_spec = tokens[0];
    if (size(tokens) < 2 || tokens[1].empty()) {
        cfg.descriptors_shift = DEFAULT_EXEC_RING_DESCRIPTORS_SHIFT;
    }
    else if (auto err = try_parse_int_token(tokens[1], &cfg.descriptors_shift);
             !empty(err)) {
        return std::unexpected(
            std::format("parse error in ring_shift `{}`: {}", tokens[1], err));
    }

    if (size(tokens) < 3 || tokens[2].empty()) {
        cfg.payload_buf_shift = DEFAULT_EXEC_RING_PAYLOAD_BUF_SHIFT;
    }
    else if (auto err = try_parse_int_token(tokens[2], &cfg.payload_buf_shift);
             !empty(err)) {
        return std::unexpected(std::format(
            "parse error in payload_buffer_shift `{}`: {}", tokens[2], err));
    }

    return cfg;
}

int init_execution_event_recorder(EventRingConfig ring_config)
{
    // Create with rw-rw-r--
    constexpr mode_t mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;

    if (!ring_config.event_ring_spec.contains('/')) {
        // The event ring specification does not contain a '/' character; this
        // is interpreted as a filename in the default event ring directory,
        // as computed by `monad_event_open_ring_dir_fd`
        char event_ring_dir_path_buf[PATH_MAX];
        int const rc = monad_event_open_ring_dir_fd(
            nullptr, event_ring_dir_path_buf, sizeof event_ring_dir_path_buf);
        if (rc != 0) {
            LOG_ERROR(
                "open of event ring default directory failed: {}",
                monad_event_ring_get_last_error());
            return rc;
        }
        ring_config.event_ring_spec = std::string{event_ring_dir_path_buf} +
                                      '/' + ring_config.event_ring_spec;
    }

    // Open the file and acquire a BSD-style exclusive lock on it; note there
    // is no O_TRUNC here because it might already exist and we might not own
    // it (e.g., if we're racing against another execution daemon started
    // accidentally). In that case we'll either win or lose the race to acquire
    // the lock, and will resize it only if we end up winning
    char const *const ring_path = ring_config.event_ring_spec.c_str();
    int ring_fd [[gnu::cleanup(cleanup_close)]] =
        open(ring_path, O_RDWR | O_CREAT, mode);
    if (ring_fd == -1) {
        int const rc = errno;
        LOG_ERROR(
            "open failed for event ring file `{}`: {} [{}]",
            ring_path,
            strerror(rc),
            rc);
        return rc;
    }
    if (flock(ring_fd, LOCK_EX | LOCK_NB) == -1) {
        int const saved_errno = errno;
        if (saved_errno == EWOULDBLOCK) {
            pid_t owner_pid = 0;
            size_t owner_pid_size = 1;

            // Another process has the exclusive lock; find out who it is
            (void)monad_event_ring_find_writer_pids(
                ring_fd, &owner_pid, &owner_pid_size);
            if (owner_pid == 0) {
                LOG_ERROR(
                    "event ring file `{}` is owned by an unknown other process",
                    ring_path);
            }
            else {
                LOG_ERROR(
                    "event ring file `{}` is owned by pid {}",
                    ring_path,
                    owner_pid);
            }
            return saved_errno;
        }
        LOG_ERROR(
            "flock on event ring file `{}` failed: {} ({})",
            ring_path,
            strerror(saved_errno),
            saved_errno);
        return saved_errno;
    }

    // monad_event_ring_init_simple uses fallocate(2), which is more general
    // but won't shrink the file; that's not appropriate here since we're the
    // exclusive owner; truncate it to zero first
    if (ftruncate(ring_fd, 0) == -1) {
        int const saved_errno = errno;
        LOG_ERROR(
            "ftruncate to zero failed for event ring file `{}` ({})",
            ring_path,
            strerror(saved_errno),
            saved_errno);
        return saved_errno;
    }

    // We're the exclusive owner; initialize the event ring file
    monad_event_ring_simple_config const simple_cfg = {
        .descriptors_shift = ring_config.descriptors_shift,
        .payload_buf_shift = ring_config.payload_buf_shift,
        .context_large_pages = 0,
        .content_type = MONAD_EVENT_CONTENT_TYPE_EXEC,
        .schema_hash = g_monad_exec_event_schema_hash};
    if (int const rc =
            monad_event_ring_init_simple(&simple_cfg, ring_fd, 0, ring_path)) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        return rc;
    }

    // Check if the underlying filesystem supports MAP_HUGETLB
    bool fs_supports_hugetlb;
    if (int const rc = monad_check_path_supports_map_hugetlb(
            ring_path, &fs_supports_hugetlb)) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        return rc;
    }
    if (!fs_supports_hugetlb) {
        LOG_WARNING(
            "file system hosting event ring file `{}` does not support "
            "MAP_HUGETLB!",
            ring_path);
    }
    int const mmap_extra_flags =
        fs_supports_hugetlb ? MAP_POPULATE | MAP_HUGETLB : MAP_POPULATE;

    // mmap the event ring into this process' address space
    monad_event_ring exec_ring;
    if (int const rc = monad_event_ring_mmap(
            &exec_ring,
            PROT_READ | PROT_WRITE,
            mmap_extra_flags,
            ring_fd,
            0,
            ring_path)) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        return rc;
    }

    // Create the execution recorder object
    // TODO(ken): this is part of the next event ring PR
    return 0;
}

MONAD_NAMESPACE_END
