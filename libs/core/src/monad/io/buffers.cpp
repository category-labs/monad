#include <bits/types/struct_iovec.h>
#include <monad/io/buffers.hpp>

#include <monad/core/assert.h>

#include <monad/io/config.hpp>
#include <monad/io/ring.hpp>

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
        do_register_buffers(const_cast<io_uring *>(&ring_.get_ring()), iov, 1);
        do_register_buffers(
            const_cast<io_uring *>(&wr_ring_->get_ring()), iov + 1, 1);
    }
    else if (!write_buf_.has_value()) {
        iovec const iov[2]{
            {.iov_base = read_buf_.get_data(),
             .iov_len = read_buf_.get_size()}};
        do_register_buffers(const_cast<io_uring *>(&ring_.get_ring()), iov, 1);
    }
    else {
        iovec const iov[2]{
            {.iov_base = read_buf_.get_data(), .iov_len = read_buf_.get_size()},
            {.iov_base = write_buf_.value().get_data(),
             .iov_len = write_buf_.value().get_size()}};
        do_register_buffers(const_cast<io_uring *>(&ring_.get_ring()), iov, 2);
    }
}

Buffers::~Buffers()
{
    if (wr_ring_ != nullptr) {
        MONAD_ASSERT(!io_uring_unregister_buffers(
            const_cast<io_uring *>(&wr_ring_->get_ring())));
    }
    MONAD_ASSERT(!io_uring_unregister_buffers(
        const_cast<io_uring *>(&ring_.get_ring())));
}

MONAD_IO_NAMESPACE_END
