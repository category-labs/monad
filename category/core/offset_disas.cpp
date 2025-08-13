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

#include <category/core/config.hpp>

#include <category/core/offset.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

namespace disas
{
    void off48_from_int(off48_t *const result, int64_t const *const offset)
    {
        *result = off48_t{*offset};
    }

    void off48_to_int(int64_t *const result, off48_t const *const offset)
    {
        *result = int64_t{*offset};
    }
}

MONAD_NAMESPACE_END
