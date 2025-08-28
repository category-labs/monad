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

#include <category/core/backtrace.hpp>
#include <category/core/config.hpp>
#include <category/core/likely.h>

#include <evmc/evmc.h>

#include <unistd.h>

MONAD_NAMESPACE_BEGIN

/// Exception for `MONAD_THROW` assertion failure.
class MonadException
{
public:
    MonadException(
        char const *message,
        char const *expr,
        char const *function,
        char const *file,
        long line);

    ~MonadException();

    char const *message() const noexcept;
    void print(int fd = STDERR_FILENO) const noexcept;

    static constexpr size_t message_buffer_size = 128;
    static constexpr size_t stack_trace_buffer_size = 16384;

private:
    char const *expr_;
    char const *function_;
    char const *file_;
    long line_;
    void *stack_trace_buffer_;
    stack_backtrace::ptr stack_trace_;
    char message_[message_buffer_size];
};

// Size of `MonadException` plus the size of exception headers must be
// smaller than 1kB for `MonadException` to fit in an emergency buffer.
// See Itanium C++ ABI: Exception Handling (Revision 1.22), Section 3.4.1.
// The size of an exception header is ~80 bytes according to Itanium C++
// ABI: Exception Handling (Revision 1.22), Section 2.2.1. It therefore
// seems safe to assume that the exception header will not become larger
// than 512 bytes. So if `MonadException` is smaller than 512 bytes, then
// the sum is smaller than 1kB.
static_assert(sizeof(MonadException) < 512);

MONAD_NAMESPACE_END

/// Given `bool expr` and 'char const *message', throw
/// `monad::MonadException` iff `expr` evaluates to `false`.
#define MONAD_THROW(expr, message)                                             \
    if (MONAD_LIKELY(expr)) { /* likeliest */                                  \
    }                                                                          \
    else {                                                                     \
        throw monad::MonadException{                                           \
            (message),                                                         \
            #expr,                                                             \
            __extension__ __PRETTY_FUNCTION__,                                 \
            __FILE__,                                                          \
            __LINE__};                                                         \
    }
