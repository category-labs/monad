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

/**
 * @file
 *
 * This file defines the function `monad_stack_backtrace_capture_and_print`,
 * which is called by the MONAD_ASSERT macro if an assertion fails. In the
 * execution daemon, most of the work is done by Boost.Stacktrace.
 *
 * Although there is little harm in taking this dependency ourselves, third
 * party users of the SDK may not want to use this library. If they use an
 * SDK function which asserts, they will will need to provide this symbol
 * to the linker. This file serves as an example of how to do this using
 * the C++23 <stacktrace>.
 */

#include <version>

#include <stddef.h>
#include <stdio.h>
#include <string.h>

#if defined(__cpp_lib_stacktrace)

    #include <stacktrace>

extern "C" void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool /*print_async_unsafe_info*/)
{
    // The implementation gives a fixed-sized buffer into which to write
    // the stack return addresses, so that this function can be used in
    // contexts where it is not safe to allocate memory. We don't currently do
    // the work of wiring fixed-sized buffers up to the C++ allocator interface,
    // so for now we just ignore these parameters.
    (void)buffer, (void)size;

    char indent_buffer[64];
    memset(indent_buffer, ' ', 64);
    indent_buffer[indent] = 0;

    for (std::stacktrace_entry const &e : std::stacktrace::current()) {
        dprintf(
            fd,
            "%s%s @ %s:%u\n",
            indent_buffer,
            e.description().c_str(),
            e.source_file().c_str(),
            e.source_line());
    }
}

#else // defined(__cpp_lib_stacktrace)

extern "C" void monad_stack_backtrace_capture_and_print(
    char *, size_t, int fd, unsigned indent, bool)
{
    // You may want to use shim-backtrace.c from the SDK example code if
    // your C++ standard library has no backtracing function
    char indent_buffer[64];
    memset(indent_buffer, ' ', 64);
    indent_buffer[indent] = 0;
    dprintf(fd, "%s stacktrace not available", indent_buffer);
}

#endif
