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

#include <boost/stacktrace/detail/frame_decl.hpp>
#include <boost/stacktrace/stacktrace.hpp>

#include <algorithm>
#include <cassert>
#include <cstdarg>
#include <cstddef>
#include <cstdio>
#include <cstring>
#include <memory>
#include <span>
#include <stdlib.h>
#include <type_traits>

#include <unistd.h>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    template <class T>
    class FixedBufferAllocator
    {
        template <class U>
        friend class FixedBufferAllocator;

        std::span<std::byte> const buffer;
        std::byte *&p;

    public:
        using value_type = T;
        using size_type = std::size_t;
        using difference_type = std::ptrdiff_t;
        using propagate_on_container_move_assignment = std::true_type;
        using is_always_equal = std::true_type;

        constexpr FixedBufferAllocator(
            std::span<std::byte> buffer_, std::byte *&p_)
            : buffer(buffer_)
            , p(p_)
        {
            p = buffer.data();
        }

        template <class U>
        constexpr FixedBufferAllocator( // NOLINT
            FixedBufferAllocator<U> const &o)
            : buffer(o.buffer)
            , p(o.p)
        {
        }

        [[nodiscard]] constexpr value_type *allocate(std::size_t n)
        {
            auto *newp = p + sizeof(value_type) * n;
            assert(size_t(newp - buffer.data()) <= buffer.size());
            auto *ret = reinterpret_cast<value_type *>(p);
            p = newp;
            return ret;
        }

        constexpr void deallocate(value_type *, std::size_t) {}
    };
}

struct stack_backtrace_impl final : public stack_backtrace
{
    using byte_allocator_type = detail::FixedBufferAllocator<std::byte>;
    using stacktrace_allocator_type =
        std::allocator_traits<byte_allocator_type>::rebind_alloc<
            ::boost::stacktrace::stacktrace::allocator_type::value_type>;
    using stacktrace_implementation_type =
        ::boost::stacktrace::basic_stacktrace<stacktrace_allocator_type>;

    std::byte *storage_end{nullptr};
    byte_allocator_type main_alloc;
    stacktrace_implementation_type stacktrace;

    explicit stack_backtrace_impl(std::span<std::byte> storage)
        : main_alloc(storage, storage_end)
        , stacktrace(stacktrace_allocator_type{main_alloc})
    {
    }

    virtual void print(
        int fd, unsigned indent,
        bool print_async_signal_unsafe_info) const noexcept override
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
        for (auto const &frame : stacktrace) {
            write("\n%s   %p", indent_buffer, frame.address());
        }
        if (print_async_signal_unsafe_info) {
            write(
                "\n\n%sAttempting async signal unsafe human readable "
                "stacktrace (this may hang):",
                indent_buffer);
            for (auto const &frame : stacktrace) {
                write("\n%s   %p:", indent_buffer, frame.address());
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
stack_backtrace::capture(std::span<std::byte> storage) noexcept
{
    assert(storage.size() > sizeof(stack_backtrace_impl));
    return ptr(new (storage.data()) stack_backtrace_impl(
        storage.subspan(sizeof(stack_backtrace_impl))));
}

extern "C" void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool print_async_unsafe_info)
{
    stack_backtrace::capture({reinterpret_cast<std::byte *>(buffer), size})
        ->print(fd, indent, print_async_unsafe_info);
}

MONAD_NAMESPACE_END
