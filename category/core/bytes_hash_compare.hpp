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

#pragma once

#include <category/core/config.hpp>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#include <komihash.h>
#pragma GCC diagnostic pop

MONAD_NAMESPACE_BEGIN

template <class Bytes>
struct BytesHashCompare
{
    size_t hash(Bytes const &a) const
    {
        return komihash(a.bytes, sizeof(Bytes), 0);
    }

    bool equal(Bytes const &a, Bytes const &b) const
    {
        return memcmp(a.bytes, b.bytes, sizeof(Bytes)) == 0;
    }

    bool operator()(Bytes const &a) const
    {
        return hash(a);
    }
};

MONAD_NAMESPACE_END
