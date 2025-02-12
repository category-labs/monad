#include <monad/io/ring.hpp>

#include <monad/io/config.hpp>

#include <monad/core/assert.h>
#include <monad/core/cmemory.hpp>

#include <liburing.h>
#include <liburing/io_uring.h>
#include <string.h>

MONAD_IO_NAMESPACE_BEGIN

Ring::Ring(RingConfig const &config)
    : ring_{}
    , params_{[&] {
        io_uring_params ret;
        cmemset(reinterpret_cast<char *>(&ret), char(0), sizeof(ret));
        if (config.sq_thread_cpu) {
            ret.flags |= IORING_SETUP_SQPOLL | IORING_SETUP_SQ_AFF;
            ret.sq_thread_cpu = *config.sq_thread_cpu;
            ret.sq_thread_idle = 60 * 1000;
        }
        if (config.enable_io_polling) {
            ret.flags |= IORING_SETUP_IOPOLL;
        }
        return ret;
    }()}
{
    int const result = io_uring_queue_init_params(
        config.entries, &ring_, const_cast<io_uring_params *>(&params_));
    MONAD_ASSERT_PRINTF(
        result == 0,
        "io_uring_queue_init_params failed: %s (%d)",
        strerror(-result),
        -result);
}

Ring::~Ring()
{
    io_uring_queue_exit(&ring_);
}

MONAD_IO_NAMESPACE_END
