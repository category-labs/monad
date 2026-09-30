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

#include <category/core/backtrace.hpp>
#include <category/core/config.hpp>

#include <boost/stacktrace/frame.hpp>
#include <boost/stacktrace/safe_dump_to.hpp>

#include <algorithm>
#include <cstdarg>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <memory>
#include <new> // IWYU pragma: keep
#include <span>
#include <stdlib.h>

#include <unistd.h>

MONAD_NAMESPACE_BEGIN

using backtrace_address = boost::stacktrace::frame::native_frame_ptr_t;

struct alignas(backtrace_address) stack_backtrace_impl final
    : public stack_backtrace
{
    std::span<backtrace_address const> frames;

    explicit stack_backtrace_impl(
        std::span<backtrace_address> const storage) noexcept
    {
        // The count includes a terminating null address. Deep stacks retain
        // the innermost frames that fit in the supplied storage.
        size_t const written = boost::stacktrace::safe_dump_to(
            static_cast<void *>(storage.data()), storage.size_bytes());
        frames = storage.first(written == 0 ? 0 : written - 1);
    }

    virtual void print(
        int const fd, unsigned const indent,
        bool const print_async_signal_unsafe_info) const noexcept override
    {
        char indent_buffer[64];
        memset(indent_buffer, ' ', 64);
        indent_buffer[indent] = 0;
        auto write = [&](char const *fmt,
                         ...) __attribute__((format(printf, 2, 3))) {
            va_list args;
            va_start(args, fmt);
            char buffer[1024];
            // NOTE: sprintf may call malloc, and is not guaranteed async
            // signal safe. Chances are very good it will be async signal
            // safe for how we're using it here.
            auto const written = std::min(
                size_t(::vsnprintf(buffer, sizeof(buffer), fmt, args)),
                sizeof(buffer));
            if (-1 == ::write(fd, buffer, written)) {
                abort();
            }
            va_end(args);
        };
        for (auto const *const address : frames) {
            write("\n%s   %p", indent_buffer, address);
        }
        if (print_async_signal_unsafe_info) {
            write(
                "\n\n%sAttempting async signal unsafe human readable "
                "stacktrace (this may hang):",
                indent_buffer);
            for (auto const *const address : frames) {
                boost::stacktrace::frame const frame{address};
                write("\n%s   %p:", indent_buffer, address);
                write(" %s", frame.name().c_str());
                if (frame.source_line() > 0) {
                    write(
                        "\n%s                   [%s:%zu]",
                        indent_buffer,
                        frame.source_file().c_str(),
                        frame.source_line());
                }
            }
        }
        write("\n");
    }
};

stack_backtrace::ptr
stack_backtrace::capture(std::span<std::byte> const storage) noexcept
{
    void *address = storage.data();
    size_t remaining = storage.size();
    if (!std::align(
            alignof(stack_backtrace_impl),
            sizeof(stack_backtrace_impl),
            address,
            remaining) ||
        remaining <= sizeof(stack_backtrace_impl)) {
        ::abort();
    }
    size_t const padding = storage.size() - remaining;
    auto const scratch =
        storage.subspan(padding + sizeof(stack_backtrace_impl));
    // alignas on the implementation also aligns the storage immediately
    // following it, because sizeof includes its trailing padding.
    size_t const capacity = scratch.size() / sizeof(backtrace_address);
    auto *const addresses = ::new (scratch.data()) backtrace_address[capacity];
    return ptr(new (address) stack_backtrace_impl({addresses, capacity}));
}

extern "C" void monad_stack_backtrace_capture_and_print(
    char *const buffer, size_t const size, int const fd, unsigned const indent,
    bool const print_async_unsafe_info)
{
    stack_backtrace::capture({reinterpret_cast<std::byte *>(buffer), size})
        ->print(fd, indent, print_async_unsafe_info);
}

MONAD_NAMESPACE_END
