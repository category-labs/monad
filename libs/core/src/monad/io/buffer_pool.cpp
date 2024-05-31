#include <monad/io/buffer_pool.hpp>

#include <monad/io/buffers.hpp>
#include <monad/io/config.hpp>

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
