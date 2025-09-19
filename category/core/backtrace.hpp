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

#pragma once

#include <category/core/config.hpp>

#include <cstddef>
#include <memory>
#include <span>

MONAD_NAMESPACE_BEGIN

/*! \brief An async signal safe stack backtracer.
 */
class stack_backtrace
{
protected:
    stack_backtrace() = default;

    struct deleter_
    {
        void operator()(stack_backtrace *p)
        {
            p->~stack_backtrace();
            // no deallocation needed
        }
    };

public:
    virtual ~stack_backtrace() = default;
    stack_backtrace(stack_backtrace const &) = delete;
    stack_backtrace(stack_backtrace &&) = delete;
    stack_backtrace &operator=(stack_backtrace const &) = delete;
    stack_backtrace &operator=(stack_backtrace &&) = delete;

    using ptr = std::unique_ptr<stack_backtrace, deleter_>;

    /*! \brief Capture a stack backtrace using the storage supplied. ASYNC
    SIGNAL SAFE.

    The buffer MUST remain within lifetime until the returned
    unique ptr is destructed. If the input buffer is not big enough, the
    process will be terminated.
    */
    static ptr capture(std::span<std::byte> storage) noexcept;

    /*! \brief Construct a stack backtrace by deserialising it from the buffer.
    ASYNC SIGNAL SAFE.
    */
    static ptr deserialize(
        std::span<std::byte> storage,
        std::span<std::byte const> serialised) noexcept;

    /*! \brief Serialise this stack backtrace into the buffer, returning the
    number of bytes serialised. ASYNC SIGNAL SAFE.

    \note The returned value may be larger that the buffer supplied, in which
    case the operation failed and you need to supply a larger buffer of the
    size specified. Passing in an empty span is allowed, but remember `malloc`
    is not async signal safe so dynamically allocated buffers may not be
    possible.
    */
    virtual size_t
    serialize(std::span<std::byte> serialised) const noexcept = 0;

    /*! \brief Print this stack backtrace in a human readable format to
    the specified file descriptor. ASYNC SIGNAL SAFE (probably).

    This call will be async signal safe if your platform's `snprintf()`
    is async signal safe for the very simple uses we use it for. This
    is not guaranteed, `snprintf()` is allowed to call `malloc()` or
    use locale functions, both of which are highly async signal unsafe.
    However for printing integers it is usually async signal safe.

    You have an option of printing function name, source file and line
    number, however these are highly async signal unsafe. If you need to
    do this, serialise the stack trace and print it elsewhere.
    */
    virtual void print(
        int fd, unsigned indent,
        bool print_async_signal_unsafe_info) const noexcept = 0;
};

MONAD_NAMESPACE_END
