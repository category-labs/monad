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

#include <category/core/terminate_handler.h>

#include <cxxabi.h>
#include <exception>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <typeinfo>
#include <unistd.h>

extern char const *__progname; // NOLINT(bugprone-reserved-identifier)

extern "C" void monad_stack_backtrace_capture_and_print(
    char *buffer, size_t size, int fd, unsigned indent,
    bool print_async_unsafe_info);

namespace
{
    void monad_terminate_handler_impl() noexcept
    {
        char buffer[16384];
        ssize_t written = 0;

        // Print header
        written = snprintf(
            buffer,
            sizeof(buffer),
            "\n"
            "=================================================================="
            "==============\n"
            "%s: std::terminate() called\n"
            "=================================================================="
            "==============\n",
            __progname);

        if (written > 0 && (size_t)written < sizeof(buffer)) {
            if (write(STDERR_FILENO, buffer, (size_t)written) == -1) {
                // Suppress warning
            }
        }

        // Try to get exception information
        std::type_info *exception_type = abi::__cxa_current_exception_type();
        if (exception_type != nullptr) {
            char const *exception_name = exception_type->name();

            // Try to demangle the name
            int status = 0;
            char *demangled =
                abi::__cxa_demangle(exception_name, nullptr, nullptr, &status);
            char const *display_name = (status == 0 && demangled != nullptr)
                                           ? demangled
                                           : exception_name;

            written = snprintf(
                buffer,
                sizeof(buffer),
                "Reason: Uncaught exception\n"
                "Exception type: %s\n",
                display_name);

            if (written > 0 && (size_t)written < sizeof(buffer)) {
                if (write(STDERR_FILENO, buffer, (size_t)written) == -1) {
                    // Suppress warning
                }
            }

            // Try to get exception message if it's a std::exception
            try {
                std::rethrow_exception(std::current_exception());
            }
            catch (std::exception const &e) {
                written = snprintf(
                    buffer,
                    sizeof(buffer),
                    "Exception message: %s\n",
                    e.what());

                if (written > 0 && (size_t)written < sizeof(buffer)) {
                    if (write(STDERR_FILENO, buffer, (size_t)written) == -1) {
                        // Suppress warning
                    }
                }
            }
            catch (...) {
                // Not a std::exception, no message available
                char const *msg = "Exception message: <not a std::exception>\n";
                if (write(STDERR_FILENO, msg, strlen(msg)) == -1) {
                    // Suppress warning
                }
            }

            if (demangled != nullptr) {
                free(demangled);
            }
        }
        else {
            // No active exception - std::terminate() was called for another
            // reason.
            char const *msg = "No active exception detected\n";
            if (write(STDERR_FILENO, msg, strlen(msg)) == -1) {
                // Suppress warning
            }
        }

        char const *separator = "----------------------------------------------"
                                "----------------------------------\n"
                                "Stack trace:\n"
                                "----------------------------------------------"
                                "----------------------------------\n";
        if (write(STDERR_FILENO, separator, strlen(separator)) == -1) {
            // Suppress warning
        }

        monad_stack_backtrace_capture_and_print(
            buffer, sizeof(buffer), STDERR_FILENO, 3, true);

        char const *footer = "================================================="
                             "===============================\n"
                             "Aborting process...\n"
                             "================================================="
                             "===============================\n";
        if (write(STDERR_FILENO, footer, strlen(footer)) == -1) {
            // Suppress warning
        }
        abort();
    }
}

extern "C" void monad_set_terminate_handler()
{
    std::set_terminate(monad_terminate_handler_impl);
}
