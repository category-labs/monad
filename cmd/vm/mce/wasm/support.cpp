// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/runtime/math/intrinsics.hpp>

#include <cstdio>
#include <cstdlib>

extern "C" [[noreturn]] void monad_assertion_failed(
    char const *expr, char const *function, char const *file, long line,
    char const *msg)
{
    std::fprintf(
        stderr,
        "%s:%ld: %s: %s %s\n",
        file,
        line,
        function,
        expr ? expr : "abort",
        msg ? msg : "");
    std::abort();
}

// Multiplication is also used by the compiler's constant folder.
extern "C" void monad_vm_runtime_mul(
    monad::uint256_t *result, monad::uint256_t const *left,
    monad::uint256_t const *right) noexcept
{
    *result = *left * *right;
}
