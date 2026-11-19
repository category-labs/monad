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

#include <category/core/io/ring.hpp>

#include <category/core/io/config.hpp>

#include <category/core/assert.h>
#include <category/core/config.hpp>

#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <expected>
#include <optional>
#include <ranges>
#include <string>
#include <string_view>
#include <system_error>

#include <fcntl.h>
#include <liburing.h>
#include <liburing/io_uring.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// The kernel prints the SQPOLL thread's times only if it wins a trylock on the
// lock that thread holds while submitting. Submission bursts are short, so an
// immediate retry usually gets through.
constexpr unsigned FDINFO_READ_ATTEMPTS = 4;

// The rest of the line that starts with `key`, leading blanks skipped.
std::optional<std::string_view>
fdinfo_value(std::string_view const text, std::string_view const key) noexcept
{
    for (auto const part : std::views::split(text, '\n')) {
        std::string_view line{part};
        if (!line.starts_with(key)) {
            continue;
        }
        line.remove_prefix(key.size());
        size_t const start = line.find_first_not_of(" \t");
        return start == std::string_view::npos ? std::string_view{}
                                               : line.substr(start);
    }
    return std::nullopt;
}

std::optional<uint64_t>
fdinfo_u64(std::string_view const text, std::string_view const key) noexcept
{
    auto const value = fdinfo_value(text, key);
    if (!value.has_value()) {
        return std::nullopt;
    }
    uint64_t out{0};
    char const *const begin = value->data();
    char const *const end = begin + value->size();
    auto const [ptr, ec] = std::from_chars(begin, end, out);
    if (ec != std::errc{} || ptr != end) {
        return std::nullopt;
    }
    return out;
}

std::optional<std::string> read_fdinfo(int const fd)
{
    std::string const path = "/proc/self/fdinfo/" + std::to_string(fd);
    int const file = ::open(path.c_str(), O_RDONLY | O_CLOEXEC);
    if (file == -1) {
        return std::nullopt;
    }
    std::string text;
    char buffer[4096];
    ssize_t n;
    while ((n = ::read(file, buffer, sizeof(buffer))) > 0) {
        text.append(buffer, static_cast<size_t>(n));
    }
    ::close(file);
    if (n < 0) {
        return std::nullopt;
    }
    return text;
}

// A lost trylock prints no SqThread line from Linux 6.15 on, and `SqThread: -1`
// with zero times before that, as does a read racing the thread's exit.
bool shows_sqpoll_thread(std::string_view const fdinfo) noexcept
{
    return fdinfo_u64(fdinfo, "SqThread:").value_or(0) != 0;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_IO_NAMESPACE_BEGIN

std::expected<SqPollTimes, SqPollTimesUnavailable>
parse_sqpoll_times(std::string_view const fdinfo) noexcept
{
    if (!shows_sqpoll_thread(fdinfo)) {
        return std::unexpected{SqPollTimesUnavailable::contended};
    }
    auto const total_us = fdinfo_u64(fdinfo, "SqTotalTime:");
    auto const work_us = fdinfo_u64(fdinfo, "SqWorkTime:");
    if (!total_us.has_value() || !work_us.has_value()) {
        return std::unexpected{SqPollTimesUnavailable::unsupported};
    }
    return SqPollTimes{
        .total_ns = *total_us * 1000, .work_ns = *work_us * 1000};
}

Ring::Ring(RingConfig const &config)
    : ring_{}
    , params_{[&] {
        io_uring_params ret;
        std::memset(&ret, 0, sizeof(ret));
        if (config.sq_thread_cpu) {
            ret.flags |= IORING_SETUP_SQPOLL | IORING_SETUP_SQ_AFF;
            ret.sq_thread_cpu = *config.sq_thread_cpu;
            ret.sq_thread_idle = 60 * 1000;
        }
        return ret;
    }()}
{
    int const result = io_uring_queue_init_params(
        config.entries, &ring_, const_cast<io_uring_params *>(&params_));
    MONAD_ASSERT_PRINTF(
        result == 0,
        "io_uring_queue_init_params failed: %s (%d)",
        strerror(-result),
        -result);
}

Ring::~Ring()
{
    io_uring_queue_exit(&ring_);
}

std::expected<SqPollTimes, SqPollTimesUnavailable> Ring::sqpoll_times() const
{
    if (!(params_.flags & IORING_SETUP_SQPOLL)) {
        return std::unexpected{SqPollTimesUnavailable::no_sqpoll};
    }
    for (unsigned attempt = 0; attempt < FDINFO_READ_ATTEMPTS; ++attempt) {
        auto const text = read_fdinfo(ring_.ring_fd);
        if (!text.has_value()) {
            return std::unexpected{SqPollTimesUnavailable::unreadable};
        }
        auto const times = parse_sqpoll_times(*text);
        if (times.has_value() ||
            times.error() != SqPollTimesUnavailable::contended) {
            return times;
        }
    }
    return std::unexpected{SqPollTimesUnavailable::contended};
}

MONAD_IO_NAMESPACE_END
