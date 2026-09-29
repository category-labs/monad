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

#pragma once

// These operator delete overloads are empty in zkvm/core/libstdcxx.cpp.
// Mark them const so GCC can remove calls and argument preparation.
// CMake injects this header into every ZisK C++ file; the official-build audit
// checks inclusion and the empty definitions.
// Keep declarations here: replaceable operator delete cannot be inline.

#include <cstddef>

#pragma GCC diagnostic push
// Suppress GCC's warning about const on void functions: these are no-ops.
#pragma GCC diagnostic ignored "-Wattributes"

[[gnu::const]] void operator delete(void *) noexcept;
[[gnu::const]] void operator delete[](void *) noexcept;
[[gnu::const]] void operator delete(void *, std::size_t) noexcept;
[[gnu::const]] void operator delete[](void *, std::size_t) noexcept;

// Expose the no-op free in zkvm/core/libc.cpp so GCC can remove calls.
// Omit noexcept to match newlib's declaration.
extern "C" [[gnu::const]] void free(void *);

#pragma GCC diagnostic pop
