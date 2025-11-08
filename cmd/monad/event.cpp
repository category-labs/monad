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

#include <category/core/assert.h>
#include <category/core/cleanup.h> //NOLINT(misc-include-cleaner)
#include <category/core/config.hpp>
#include <category/core/event/event_ring.h>
#include <category/core/event/event_ring_util.h>
#include <category/execution/ethereum/event/exec_event_ctypes.h>
#include <category/execution/ethereum/event/exec_event_recorder.hpp>

#include <charconv>
#include <concepts>
#include <expected>
#include <filesystem>
#include <format>
#include <memory>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

#include <errno.h>
#include <fcntl.h>
#include <linux/limits.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/file.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <unistd.h>

#include <quill/LogLevel.h>
#include <quill/Quill.h>

namespace fs = std::filesystem;

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

int claim_event_ring_file(fs::path const &ring_path)
{
    int ring_fd [[gnu::cleanup(cleanup_close)]] =
        open(ring_path.c_str(), O_RDONLY);
    if (ring_fd == -1) {
        // Inability to open is normal: it means there's no zombie to clean up
        return 0;
    }
    if (flock(ring_fd, LOCK_EX | LOCK_NB) == -1) {
        int const saved_errno = errno;
        if (saved_errno == EWOULDBLOCK) {
            pid_t owner_pid = 0;

            // Another process has an exclusive lock; find out who it is
            (void)monad_event_ring_query_excl_writer_pid(ring_fd, &owner_pid);
            if (owner_pid == 0) {
                LOG_ERROR(
                    "event ring file `{}` is owned by an unknown other process",
                    ring_path.c_str());
            }
            else {
                LOG_ERROR(
                    "event ring file `{}` is owned by pid {}",
                    ring_path.c_str(),
                    owner_pid);
            }
            return EWOULDBLOCK;
        }
        LOG_ERROR(
            "flock on event ring file `{}` failed: {} ({})",
            ring_path.c_str(),
            strerror(saved_errno),
            saved_errno);
        return saved_errno;
    }
    (void)unlink(ring_path.c_str()); // what we now own is a zombie; destroy it
    return 0;
}

int allocate_event_ring_file(
    monad_event_ring_simple_config const &simple_cfg, fs::path const &init_path,
    fs::path const &ring_path, int *const init_ring_fd)
{
    // Create event ring files with rw-rw-r--
    constexpr mode_t CreateMode =
        S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;

    *init_ring_fd =
        open(init_path.c_str(), O_RDWR | O_CREAT | O_EXCL, CreateMode);
    if (*init_ring_fd == -1) {
        int const rc = errno;
        LOG_ERROR(
            "could not create event ring temporary initialization file `{}` "
            "(for {}): "
            "{} [{}]",
            init_path.c_str(),
            ring_path.c_str(),
            strerror(rc),
            rc);
        return rc;
    }
    if (flock(*init_ring_fd, LOCK_EX) == -1) {
        int const saved_errno = errno;
        LOG_ERROR(
            "flock on event ring file temporary initialization file `{}` (for "
            "{}) failed: {} ({})",
            init_path.c_str(),
            ring_path.c_str(),
            strerror(saved_errno),
            saved_errno);
        return saved_errno;
    }
    if (int const rc = monad_event_ring_init_simple(
            &simple_cfg, *init_ring_fd, 0, init_path.c_str())) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        return rc;
    }
    return 0;
}

// Create an event ring file which we own exclusively. This is tricky because
// as soon as we open a file with O_RDWR or O_WRONLY, any API user calling the
// function monad_event_ring_query_excl_writer_pid might assume the file is
// ready to be used. Unless they're careful, they could mmap a half-initialized
// file, which gives confusing errors.
//
// This will create a new locked file that is fully initialized, and then
// rename it to the correct name using Linux's renameat2(2) RENAME_NOREPLACE
// feature.
//
//   1. First we try to take possession of the file's name (on an advisory
//      basis using flock(2)) via the helper function `claim_event_ring_file`.
//      It places a LOCK_EX flock(2) to claim ownership of the initialization
//      process, and returns EWOULDBLOCK if it appears another process already
//      owns the file. If we claim the file, then (1) it existed and (2) was
//      un-owned and was therefore a zombie from a crashed process. We destroy
//      it.
//
//   2. Next, we use the helper function `allocate_event_ring_file` to create
//      the real file (called the "init" file) with the temporary file name
//      `<file-name>.<our-pid>`; when this returns successfully, the file is
//      advisory-locked and initialized
//
//   3. Finally, we rename the init file to its correct filename
int create_owned_event_ring(
    fs::path const &ring_file_path,
    monad_event_ring_simple_config const &simple_cfg, int *ring_fd)
{
    fs::path init_file_path = ring_file_path;
    init_file_path.replace_filename(
        std::format("{}.{}", ring_file_path.filename().c_str(), getpid()));

    if (int const rc = claim_event_ring_file(ring_file_path)) {
        return rc;
    }

    if (int const rc = allocate_event_ring_file(
            simple_cfg, init_file_path, ring_file_path, ring_fd)) {
        (void)unlink(init_file_path.c_str());
        return rc;
    }

    if (renameat2(
            AT_FDCWD,
            init_file_path.c_str(),
            AT_FDCWD,
            ring_file_path.c_str(),
            RENAME_NOREPLACE) == -1) {
        int const rc = errno;
        (void)unlink(init_file_path.c_str());
        LOG_ERROR(
            "rename of {} -> {} failed: {} [{}]",
            init_file_path.c_str(),
            ring_file_path.c_str(),
            strerror(rc),
            rc);
        return rc;
    }

    return 0;
}

// Call create_owned_event_ring, but with SIGTERM and SIGINT blocked while it
// runs so we can't be killed, which would leave junk files lying around; those
// signals will be unblocked again (if they were before) to receive any pending
// signals prior to returning
int create_owned_event_ring_nointr(
    fs::path const &ring_file_path,
    monad_event_ring_simple_config const &simple_cfg, int *ring_fd)
{
    sigset_t to_block;
    sigset_t old_mask;

    sigemptyset(&to_block);
    sigaddset(&to_block, SIGINT);
    sigaddset(&to_block, SIGTERM);
    sigprocmask(SIG_BLOCK, &to_block, &old_mask);
    int const rc = create_owned_event_ring(ring_file_path, simple_cfg, ring_fd);
    sigprocmask(SIG_SETMASK, &old_mask, nullptr);
    return rc;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

// Links against the global object in libmonad_execution_ethereum; remains
// uninitialized if recording is disabled
extern std::unique_ptr<ExecutionEventRecorder> g_exec_event_recorder;

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
    cfg.event_ring_file = tokens[0];
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
    char ring_path[PATH_MAX];
    MONAD_ASSERT(!g_exec_event_recorder, "recorder initialized twice?");

    if (int const rc = monad_event_resolve_ring_file(
            MONAD_EVENT_DEFAULT_HUGETLBFS,
            ring_config.event_ring_file.c_str(),
            ring_path,
            sizeof ring_path);
        rc != 0) {
        LOG_ERROR(
            "resolution of event ring file {} failed: {}",
            ring_config.event_ring_file,
            monad_event_ring_get_last_error());
        return rc;
    }
    if (ring_config.event_ring_file != ring_path) {
        LOG_INFO(
            "event ring `{}` resolved to `{}`",
            ring_config.event_ring_file,
            ring_path);
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

    monad_event_ring_simple_config const simple_cfg = {
        .descriptors_shift = ring_config.descriptors_shift,
        .payload_buf_shift = ring_config.payload_buf_shift,
        .context_large_pages = 0,
        .content_type = MONAD_EVENT_CONTENT_TYPE_EXEC,
        .schema_hash = g_monad_exec_event_schema_hash};

    int ring_fd [[gnu::cleanup(cleanup_close)]] = -1;
    if (int const rc =
            create_owned_event_ring_nointr(ring_path, simple_cfg, &ring_fd)) {
        return rc;
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
    g_exec_event_recorder =
        std::make_unique<ExecutionEventRecorder>(ring_fd, ring_path, exec_ring);
    LOG_INFO("execution event ring created: {}", ring_path);
    return 0;
}

MONAD_NAMESPACE_END
