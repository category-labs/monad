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

// Stable include path for the immutable hash map used by the state
// subsystem. The host build re-exports immer::map as immutable::map; the
// zkVM build shadows this header with an ankerl::unordered_dense-backed
// shim that lacks immer's HAMT / thread_local free list / refcounting
// machinery (and the __popcountdi2 / __tls_get_addr / __cxa_thread_atexit
// / __cxa_guard_* symbols those drag into the link).

#pragma once

// TODO immer known to trigger incorrect warning
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#include <immer/map.hpp>
#pragma GCC diagnostic pop

namespace immutable
{
    using ::immer::map;
}
