#include <category/async/connected_operation.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/io.hpp>
#include <category/async/io_senders.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>

#include <chrono>

using monad::io::Buffers;
using monad::io::make_buffers_for_segregated_read_write;
using monad::io::Ring;
using monad::io::RingConfig;
using MONAD_ASYNC_NAMESPACE::AsyncIO;
using MONAD_ASYNC_NAMESPACE::erased_connected_operation;
using MONAD_ASYNC_NAMESPACE::read_single_buffer_sender;
using MONAD_ASYNC_NAMESPACE::storage_pool;
using MONAD_ASYNC_NAMESPACE::use_anonymous_inode_tag;

struct reinit_receiver
{
    static constexpr bool lifetime_managed_internally = false;

    void set_value(
        erased_connected_operation *io_state,
        read_single_buffer_sender::result_type rbuf)
    {
        if (!rbuf) {
            return;
        }

        // Re-submit immediately from inside completion.
        // This is what triggers re-entrancy if submit path polls.
        for (int i = 0; i < 8; ++i) {
            io_state->reinitiate();
        }
    }

    void reset() {}
};

int main()
{
    // 1) Tiny segregated rings to force SQ pressure
    RingConfig rc_rd{};
    rc_rd.entries = 4;
    RingConfig rc_wr{};
    rc_wr.entries = 4;
    Ring rd_ring(rc_rd);
    Ring wr_ring(rc_wr);

    auto bufs = monad::io::make_buffers_for_segregated_read_write(
        rd_ring,
        wr_ring,
        2, /* read count*/
        4, /* write count SQ=4 */
        AsyncIO::MONAD_IO_BUFFERS_READ_SIZE,
        AsyncIO::MONAD_IO_BUFFERS_WRITE_SIZE);

    storage_pool pool(use_anonymous_inode_tag{});

    AsyncIO aio(pool, bufs);

    aio.set_concurrent_read_io_limit(0);
    aio.set_eager_completions(false);

    using OpUPtr = AsyncIO::connected_operation_unique_ptr_type<
        read_single_buffer_sender,
        reinit_receiver>;
    std::vector<OpUPtr> ops;
    ops.reserve(32);
    for (int i = 0; i < 32; ++i) {
        ops.push_back(aio.make_connected(
            read_single_buffer_sender{
                {0, 0}, AsyncIO::MONAD_IO_BUFFERS_READ_SIZE},
            reinit_receiver{}));
    }
    for (auto &op : ops) {
        op->initiate();
    }

    auto start = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - start < std::chrono::seconds(5)) {
        aio.poll_blocking(1);
    }
}
