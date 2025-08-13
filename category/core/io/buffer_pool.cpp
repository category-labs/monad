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

#include <category/core/io/buffer_pool.hpp>

#include <category/core/io/buffers.hpp>
#include <category/core/io/config.hpp>

#include <cstddef>

MONAD_IO_NAMESPACE_BEGIN

BufferPool::BufferPool(Buffers const &buffers, bool const is_read)
    : next_{nullptr}
{
    if (is_read) {
        size_t const count = buffers.get_read_count();
        for (size_t i = 0; i < count; ++i) {
            release(buffers.get_read_buffer(i));
        }
    }
    else {
        size_t const count = buffers.get_write_count();
        for (size_t i = 0; i < count; ++i) {
            release(buffers.get_write_buffer(i));
        }
    }
}

MONAD_IO_NAMESPACE_END
