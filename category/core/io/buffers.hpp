#pragma once

#include <category/core/io/config.hpp>

#include <category/core/assert.h>
#include <category/core/mem/huge_mem.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>

MONAD_IO_NAMESPACE_BEGIN

class Ring;
class Buffers;

[[gnu::always_inline]] inline Buffers make_buffers_for_read_only(
    Ring &ring, size_t read_count, size_t read_size = 1UL << 12);

[[gnu::always_inline]] inline Buffers make_buffers_for_mixed_read_write(
    Ring &ring, size_t read_count, size_t write_count,
    size_t read_size = 1UL << 12, size_t write_size = 1UL << 16);

[[gnu::always_inline]] inline Buffers make_buffers_for_segregated_read_write(
    Ring &ring, Ring &wr_ring, size_t read_count, size_t write_count,
    size_t read_size = 1UL << 12, size_t write_size = 1UL << 16);

class Buffers final
{
    friend inline Buffers
    make_buffers_for_read_only(Ring &ring, size_t read_count, size_t read_size);
    friend inline Buffers make_buffers_for_mixed_read_write(
        Ring &ring, size_t read_count, size_t write_count, size_t read_size,
        size_t write_size);
    friend inline Buffers make_buffers_for_segregated_read_write(
        Ring &ring, Ring &wr_ring, size_t read_count, size_t write_count,
        size_t read_size, size_t write_size);

    Ring &ring_, *wr_ring_{nullptr};
    size_t const read_bits_;
    size_t const write_bits_;
    HugeMem const read_buf_;
    std::optional<HugeMem> const write_buf_;
    size_t const read_count_;
    size_t const write_count_;

    Buffers(
        Ring &, Ring *, size_t read_count, size_t write_count, size_t read_size,
        size_t write_size);

public:
    ~Buffers();

    [[gnu::always_inline]] bool is_read_only() const
    {
        return !write_buf_.has_value();
    }

    [[gnu::always_inline]] Ring &ring() const
    {
        return ring_;
    }

    [[gnu::always_inline]] Ring *wr_ring() const
    {
        return wr_ring_;
    }

    [[gnu::always_inline]] size_t get_read_count() const
    {
        return read_count_;
    }

    [[gnu::always_inline]] size_t get_write_count() const
    {
        return write_count_;
    }

    [[gnu::always_inline]] size_t get_read_size() const
    {
        return 1UL << read_bits_;
    }

    [[gnu::always_inline]] size_t get_write_size() const
    {
        return 1UL << write_bits_;
    }

    [[gnu::always_inline]] static constexpr uint16_t get_read_index()
    {
        return 0;
    }

    [[gnu::always_inline]] static constexpr uint16_t get_write_index()
    {
        return 1;
    }

    [[gnu::always_inline]] unsigned char *get_read_buffer(size_t const i) const
    {
        MONAD_DEBUG_ASSERT(i < read_count_);
        unsigned char *const ret = read_buf_.get_data() + (i << read_bits_);
        MONAD_DEBUG_ASSERT(((void)ret[0], true));
        return ret;
    }

    [[gnu::always_inline]] unsigned char *get_write_buffer(size_t const i) const
    {
        MONAD_DEBUG_ASSERT(i < write_count_);
        unsigned char *const ret =
            write_buf_.value().get_data() + (i << write_bits_);
        MONAD_DEBUG_ASSERT(((void)ret[0], true));
        return ret;
    }
};

[[gnu::always_inline]] inline Buffers
make_buffers_for_read_only(Ring &ring, size_t read_count, size_t read_size)
{
    return Buffers(ring, nullptr, read_count, 0, read_size, 0);
}

[[gnu::always_inline]] inline Buffers make_buffers_for_mixed_read_write(
    Ring &ring, size_t read_count, size_t write_count, size_t read_size,
    size_t write_size)
{
    return Buffers(
        ring, nullptr, read_count, write_count, read_size, write_size);
}

[[gnu::always_inline]] inline Buffers make_buffers_for_segregated_read_write(
    Ring &ring, Ring &wr_ring, size_t read_count, size_t write_count,
    size_t read_size, size_t write_size)
{
    return Buffers(
        ring, &wr_ring, read_count, write_count, read_size, write_size);
}

MONAD_IO_NAMESPACE_END
