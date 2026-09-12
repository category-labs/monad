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

// The guest's operator delete family is empty -- zkvm/core/libstdcxx.cpp -- because
// the allocator is a bump pointer whose free is a no-op. Those definitions are
// alone in their translation unit, so without this every other one emits a call:
// 27,851 of them on block 25815042, 9,599 from State::~State().
//
// What this buys is not the call. Once gcc knows the callee has no effect it drops
// the null test, the pointer arithmetic and the stack frame the call forced, and a
// std::vector destructor collapses to nothing.
//
// `const` is a statement of fact about those definitions, not a hint: an empty body
// examines nothing and has no effect. It stops being true the moment one of them
// gains a body, which is why zkvm/zisk/audit-official-build.py checks the
// definitions and this file's own presence on the compile line.
//
// Declarations, not inline definitions: [replacement.functions] forbids a
// replaceable operator delete from being declared inline, and this needs no such
// licence.
//
// Reaches every C++ translation unit through -include, from zkvm/guest/CMakeLists.txt.

#include <cstddef>

#pragma GCC diagnostic push
// `const` on a function returning void is exactly the case that matters: there is
// no result, and the point is that there is no effect either.
#pragma GCC diagnostic ignored "-Wattributes"

[[gnu::const]] void operator delete(void *) noexcept;
[[gnu::const]] void operator delete[](void *) noexcept;
[[gnu::const]] void operator delete(void *, std::size_t) noexcept;
[[gnu::const]] void operator delete[](void *, std::size_t) noexcept;

#pragma GCC diagnostic pop
