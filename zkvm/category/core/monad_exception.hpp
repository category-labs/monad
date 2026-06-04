// Copyright (C) 2025-26 Category Labs, Inc.
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

// zkVM shadow of category/core/monad_exception.hpp. The host's
// MONAD_ASSERT_THROW throws monad::MonadException, but the bare-metal
// RISC-V build runs with -fno-exceptions, which makes the `throw`
// expression a hard compile error. The shadow collapses the macro to
// std::abort(); MonadException itself is dropped because no
// cross-compiled TU constructs or catches it.

#pragma once

#include <category/core/config.hpp>
#include <category/core/likely.h>

#include <cstdlib>

#define MONAD_ASSERT_THROW(expr, message)                                      \
    do {                                                                       \
        if (MONAD_UNLIKELY(!(expr))) {                                         \
            std::abort();                                                      \
        }                                                                      \
    }                                                                          \
    while (0)
