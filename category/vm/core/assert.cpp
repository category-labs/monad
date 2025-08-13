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

#include <cstdlib>
#include <print>

extern char const *__progname; // NOLINT(bugprone-reserved-identifier)

extern "C" void __attribute__((noreturn)) monad_vm_assertion_failed(
    char const *expr, char const *function, char const *file, long line)
{
    std::print(
        stderr,
        "{}: {}:{}: {}: Assertion '{}' failed.\n",
        __progname,
        file,
        line,
        function,
        expr);

    std::abort();
}
