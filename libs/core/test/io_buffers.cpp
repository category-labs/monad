#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>

#include <monad/config.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <gtest/gtest.h>

TEST(HugeMem, works)
{
    using namespace MONAD_NAMESPACE;
    {
        io::Ring ring;
        io::Buffers const buffers = io::make_buffers_for_read_only(ring, 8);
    }
    {
        io::Ring ring;
        io::Buffers const buffers =
            io::make_buffers_for_mixed_read_write(ring, 8, 8);
    }
    {
        io::Ring ring1;
        io::Ring ring2;
        io::Buffers const buffers =
            io::make_buffers_for_segregated_read_write(ring1, ring2, 8, 8);
    }
}
