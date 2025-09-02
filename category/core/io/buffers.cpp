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

#include <bits/types/struct_iovec.h>
#include <category/core/io/buffers.hpp>

#include <category/core/assert.h>

#include <category/core/io/config.hpp>
#include <category/core/io/ring.hpp>

#include <liburing.h>

#include <sys/uio.h>

#include <bit>
#include <cstddef>
#include <cstring>
#include <iostream>
#include <optional>
#include <source_location>

MONAD_IO_NAMESPACE_BEGIN

Buffers::Buffers(
    Ring &ring, Ring *wr_ring, size_t const read_count,
    size_t const write_count, size_t const read_size, size_t const write_size)
    : ring_{ring}
    , wr_ring_(wr_ring)
    , read_bits_{[=] {
        MONAD_ASSERT(std::has_single_bit(read_size));
        MONAD_ASSERT(read_size >= (1UL << 12));
        return static_cast<size_t>(std::countr_zero(read_size));
    }()}
    , write_bits_{[=]() -> size_t {
        if (write_count == 0 && write_size == 0) {
            return 0;
        }
        MONAD_ASSERT(std::has_single_bit(write_size));
        MONAD_ASSERT(write_size >= (1UL << 12));
        return static_cast<size_t>(std::countr_zero(write_size));
    }()}
    , read_buf_{read_count * read_size}
    , write_buf_{(write_count == 0 && write_size == 0) ? std::optional<HugeMem>() : std::optional<HugeMem>(write_count * write_size)}
    , read_count_{read_buf_.get_size() / read_size}
    , write_count_{
          (write_count == 0 && write_size == 0)
              ? 0
              : (write_buf_->get_size() / write_size)}
{
    auto do_register_buffers = [](io_uring *const ring,
                                  const struct iovec *const iovecs,
                                  unsigned const nr_iovecs,
                                  std::source_location loc =
                                      std::source_location::current()) {
        if (int const errcode =
                io_uring_register_buffers(ring, iovecs, nr_iovecs);
            errcode < 0) {
            std::cerr
                << "FATAL: io_uring_register_buffers in buffer.cpp at line "
                << loc.line() << " failed with '" << strerror(-errcode)
                << "'. iovecs[0] = { " << iovecs[0].iov_base << ", "
                << iovecs[0].iov_len << " }" << std::endl;
            std::terminate();
        }
    };
    if (wr_ring_ != nullptr) {
        iovec const iov[2]{
            {.iov_base = read_buf_.get_data(), .iov_len = read_buf_.get_size()},
            {.iov_base = write_buf_.value().get_data(),
             .iov_len = write_buf_.value().get_size()}};
        do_register_buffers(&ring_.get_ring(), iov, 1);
        do_register_buffers(&wr_ring_->get_ring(), iov + 1, 1);
    }
    else if (!write_buf_.has_value()) {
        iovec const iov[2]{
            {.iov_base = read_buf_.get_data(),
             .iov_len = read_buf_.get_size()}};
        do_register_buffers(&ring_.get_ring(), iov, 1);
    }
    else {
        iovec const iov[2]{
            {.iov_base = read_buf_.get_data(), .iov_len = read_buf_.get_size()},
            {.iov_base = write_buf_.value().get_data(),
             .iov_len = write_buf_.value().get_size()}};
        do_register_buffers(&ring_.get_ring(), iov, 2);
    }
}

Buffers::~Buffers()
{
    if (wr_ring_ != nullptr) {
        MONAD_ASSERT(!io_uring_unregister_buffers(&wr_ring_->get_ring()));
    }
    MONAD_ASSERT(!io_uring_unregister_buffers(&ring_.get_ring()));
}

MONAD_IO_NAMESPACE_END
