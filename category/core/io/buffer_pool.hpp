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

#include <category/core/io/config.hpp>

MONAD_IO_NAMESPACE_BEGIN

class Buffers;

class BufferPool
{
    unsigned char *next_;

public:
    BufferPool(Buffers const &, bool is_read);

    [[gnu::always_inline]] unsigned char *alloc()
    {
        unsigned char *const next = next_;
        if (next) {
            next_ = *reinterpret_cast<unsigned char **>(next);
        }
        return next;
    }

    [[gnu::always_inline]] void release(unsigned char *const next)
    {
        *reinterpret_cast<unsigned char **>(next) = next_;
        next_ = next;
    }
};

static_assert(sizeof(BufferPool) == 8);
static_assert(alignof(BufferPool) == 8);

MONAD_IO_NAMESPACE_END
