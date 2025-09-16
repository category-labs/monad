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

#include <stddef.h>

#if __has_include(<backtrace.h>)
    #include <backtrace.h>
#elif __has_include(<execinfo.h>)
    #include <execinfo.h>
    #define HAS_GLIBC_BACKTRACE 1
#else
    #include <stdio.h>
#endif

// # Explanation of monad_stack_backtrace_capture_and_print
//
// The execution events SDK is intended to be used by third-party integrators,
// but it is also part of the Category Labs' implementation of a Monad
// blockchain node. It shares certain source files with the execution daemon,
// two of which are "category/core/assert.{h,c}"
//
// The event SDK prefers to return error codes and very rarely asserts, but
// some assertions are still present (e.g., checking that alignment is a power
// of two, which it always is, but which cannot always be determined at compile
// time so the compiler must emit code for the assertion failure code path).
//
// When an assertion fails, assert.c eventually calls an external function
// named `monad_stack_backtrace_capture_and_print`, which is intended to print
// a "very nice" stack trace before printing the assertion death message. Soon
// after, abort(3) is called.
//
// Generating a stack trace is easy, but decorating it with "good" symbol
// information is harder, and typically requires the implementation to parse
// the DWARF debugging information in all ELF files loaded by the dynamic
// linker. Without DWARF, only symbols in dynamic libraries will be visible,
// and even then will not contain source code locations.
//
// The execution daemon is a C++ program that has many dependencies, including
// Boost.Stacktrace which is able to parse DWARF information and produce a
// very good symbolized stack trace. The implementation of the
// `monad_stack_backtrace_capture_and_print` function used by the execution
// daemon (in the file `backtrace.cpp`) uses Boost.Stacktrace.
//
// We do not want to require third-parties to use Boost.Stacktrace as a hard
// requirement, so `monad_stack_backtrace_capture_and_print` was given
// `extern "C"` linkage, and is left as an undefined symbol in libmonad_event.a
//
// Thus, when you compile a program that links to libmonad_event.a, you are
// required to provide a definition of the
// monad_stack_backtrace_capture_and_print symbol to the linker, or your link
// will fail.
//
// You have five options:
//
//   1. The easiest is to use a trimmed down implementation that just captures
//      a stack trace but does not perform symbolization (either using a
//      library like libunwind or the backtrace(3) functions in glibc).
//      That is what this file does, for the sake of easily linking example
//      programs with no third-party libraries required by the host. Even
//      though it calls a function named `backtrace_symbols_fd`, the
//      symbolization won't be very good: at the time of this writing, the
//      <execinfo.h> backtrace functions use the symbols names reported by the
//      dynamic linker, which do not parse debugging information. Thus they
//      will only work for dynamically-linked library functions, and won't have
//      source information
//
//   2. Since C++23, the C++ standard library has a built-in stacktrace library
//      (available via <stacktrace>). It is available in libstdc++, but not
//      yet available through libc++ at this time this was written (as of LLVM
//      21). The `eventcap` program uses <stacktrace> when compiled with
//      libstdc++. The libstdc++ implementation internally uses the libbacktrace
//      C library provided by the gcc compiler project to do the heavy lifting
//
//   3. If you are using pure C, you can directly use libbacktrace yourself;
//      despite the name, this should not be confused with the backtrace(3)
//      function in <execinfo.h>, which is provided by glibc; libbacktrace is a
//      large-ish library that can perform more sophisticated symbolization
//
//   4. If you are using C++ and don't mind the dependency on Boost.Stacktrace,
//      you can use that. For an example of how to use it, you can use the
//      execution daemon's `backtrace.cpp` file
//
//   5. You can use some other library that provides good symbolized backtraces,
//      or integrate this with your existing code's "assertion death" handling
//      logic
//
// Most of this academic, as the library tends to only assert in cases which
// should never happen but the compiler cannot statically determine this.
// Certain logic bugs in the program may trigger an assertion, however.
extern void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool print_async_unsafe_info)
{
#if HAS_GLIBC_BACKTRACE
    int const n_frames =
        backtrace((void *)buffer, (int)(size / sizeof(void *)));
    backtrace_symbols_fd((void *)buffer, n_frames, fd);
    (void)indent, (void)print_async_unsafe_info;
#else
    (void)buffer, (void)size, (void)fd, (void)indent,
        (void)print_async_unsafe_info;
    fprintf(stderr, "error: backtrace not implemented\n");
#endif
}
