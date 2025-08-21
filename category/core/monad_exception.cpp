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

#include <category/core/monad_exception.hpp>

#include <cstdio>
#include <cstring>

extern char const *__progname;

MONAD_NAMESPACE_BEGIN

MonadException::MonadException(
    char const *const message,
    char const *const expr,
    char const *const function,
    char const *const file,
    long const line)
    : expr_{expr}
    , function_{function}
    , file_{file}
    , line_{line}
    , stack_trace_buffer_{std::malloc(stack_trace_buffer_size)}
{
    if (stack_trace_buffer_) {
        stack_trace_ = stack_backtrace::capture({
            reinterpret_cast<std::byte *>(stack_trace_buffer_),
            stack_trace_buffer_size});
    }
    (void)std::strncpy(message_, message, message_buffer_size - 1);
    message_[message_buffer_size - 1] = '\0';
}

MonadException::~MonadException()
{
    stack_trace_.reset();
    std::free(stack_trace_buffer_);
}

char const *MonadException::message() const noexcept
{
    return message_;
}

void MonadException::print(int fd) const noexcept
{
    if (stack_trace_buffer_) {
        stack_trace_->print(fd, 3, true);
    }
    else {
        dprintf(fd, "Memory allocation failed for stack backtrace\n");
    }
    dprintf(
        fd,
        "%s: %s:%ld: %s: Monad throw '%s' failed: '%s'\n",
        __progname,
        file_,
        line_,
        function_,
        expr_,
        message_);
}

MONAD_NAMESPACE_END
