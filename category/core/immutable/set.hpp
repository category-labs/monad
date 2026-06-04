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

// Stable include path for the immutable hash set. See [[map.hpp]].

#pragma once

// TODO immer known to trigger incorrect warning
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#include <immer/set.hpp>
#pragma GCC diagnostic pop

namespace immutable
{
    using ::immer::set;
}
