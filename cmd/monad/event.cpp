#include "event.hpp"

#include <category/core/assert.h>
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
//   <file-name>[:<descriptor-shift>:<buf-shift>]
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
            "<file-path>[:<descriptor-shift>:<payload-buffer-shift>]",
            s));
    }
    cfg.event_ring_path = tokens[0];
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

int init_execution_event_recorder(EventRingConfig const &ring_config)
{
    // Create with rw-rw-r--
    constexpr mode_t mode = S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH;
    char const *ring_path = ring_config.event_ring_path.c_str();

    // Open the file and acquire a BSD-style exclusive lock on it; note there
    // is no O_TRUNC here because it might already exist and we might not own
    // it (e.g., if we're racing against another execution daemon started
    // accidentally). In that case we'll either win or lose the race to acquire
    // the lock, and will resize it only if we end up winning
    int const ring_fd = open(ring_path, O_RDWR | O_CREAT, mode);
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
            // TODO(ken): we report who this is later in PR4, when the utility
            //    function `monad_event_ring_find_writer_pids` is added
            LOG_ERROR(
                "event ring file `{}` is owned by another process", ring_path);
            return saved_errno;
        }
        LOG_ERROR(
            "flock on event ring file `{}` failed: {} ({})",
            ring_path,
            strerror(saved_errno),
            saved_errno);
        (void)close(ring_fd);
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
        (void)close(ring_fd);
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
        (void)close(ring_fd);
        return rc;
    }

    // Check if the underlying filesystem supports MAP_HUGETLB
    bool fs_supports_hugetlb;
    if (int const rc = monad_check_path_supports_map_hugetlb(
            ring_path, &fs_supports_hugetlb)) {
        LOG_ERROR(
            "event library error -- {}", monad_event_ring_get_last_error());
        (void)close(ring_fd);
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
        (void)close(ring_fd);
        return rc;
    }

    // Create the execution recorder object
    // TODO(ken): this is part of the next event ring PR
    return 0;
}

MONAD_NAMESPACE_END
