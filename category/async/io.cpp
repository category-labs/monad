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

#include <category/async/io.hpp>

#include <category/async/concepts.hpp>
#include <category/async/config.hpp>
#include <category/async/detail/connected_operation_storage.hpp>
#include <category/async/detail/scope_polyfill.hpp>
#include <category/async/erased_connected_operation.hpp>
#include <category/async/storage_pool.hpp>
#include <category/core/assert.h>
#include <category/core/io/buffers.hpp>
#include <category/core/io/ring.hpp>
#include <category/core/tl_tid.h>
#include <category/core/unordered_map.hpp>

#include <atomic>
#include <cassert>
#include <cerrno>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <limits>
#include <memory>
#include <ostream>
#include <set>
#include <span>
#include <system_error>
#include <utility>
#include <vector>

#include <bits/types/struct_iovec.h>
#include <fcntl.h>
#include <liburing.h>
#include <liburing/io_uring.h>
#include <linux/ioprio.h>
#include <poll.h>
#include <stdlib.h>
#include <sys/resource.h> // for setrlimit
#include <unistd.h>

#define MONAD_ASYNC_IO_URING_RETRYABLE2(unique, ...)                           \
    ({                                                                         \
        int unique;                                                            \
        for (;;) {                                                             \
            unique = (__VA_ARGS__);                                            \
            if (unique < 0) {                                                  \
                if (unique == -EINTR) {                                        \
                    continue;                                                  \
                }                                                              \
                char buffer[256] = "unknown error";                            \
                if (strerror_r(-unique, buffer, 256) != nullptr) {             \
                    buffer[255] = 0;                                           \
                }                                                              \
                MONAD_ABORT_PRINTF("FATAL: %s", buffer)                        \
            }                                                                  \
            break;                                                             \
        }                                                                      \
        unique;                                                                \
    })
#define MONAD_ASYNC_IO_URING_RETRYABLE(...)                                    \
    MONAD_ASYNC_IO_URING_RETRYABLE2(BOOST_OUTCOME_TRY_UNIQUE_NAME, __VA_ARGS__)

MONAD_ASYNC_NAMESPACE_BEGIN

namespace detail
{
    // diseased dead beef in hex, last bit set so won't be a pointer
    static void *const ASYNC_IO_MSG_PIPE_READY_IO_URING_DATA_MAGIC =
        (void *)(uintptr_t)0xd15ea5eddeadbeef;

    struct AsyncIO_per_thread_state_t::within_completions_holder
    {
        AsyncIO_per_thread_state_t *parent;

        explicit within_completions_holder(AsyncIO_per_thread_state_t *parent_)
            : parent(parent_)
        {
            parent->within_completions_count++;
        }

        within_completions_holder(within_completions_holder const &) = delete;
        within_completions_holder(within_completions_holder &&) = default;

        ~within_completions_holder()
        {
            if (0 == --parent->within_completions_count) {
                parent->within_completions_reached_zero();
            }
        }
    };

    AsyncIO_per_thread_state_t::within_completions_holder
    AsyncIO_per_thread_state_t::enter_completions()
    {
        return within_completions_holder{this};
    }

    extern __attribute__((visibility("default"))) AsyncIO_per_thread_state_t &
    AsyncIO_per_thread_state()
    {
        static thread_local AsyncIO_per_thread_state_t v;
        return v;
    }

    static struct AsyncIO_rlimit_raiser_impl
    {
        AsyncIO_rlimit_raiser_impl()
        {
            struct rlimit r = {0, 0};
            getrlimit(RLIMIT_NOFILE, &r);
            if (r.rlim_cur < 4096) {
                std::cerr << "WARNING: maximum file descriptor limit is "
                          << r.rlim_cur
                          << " which is less than 4096. 'Too many open files' "
                             "errors may result. You can increase the hard "
                             "file descriptor limit for a given user by adding "
                             "to '/etc/security/limits.conf' '<username> hard "
                             "nofile 16384'."
                          << std::endl;
            }
        }
    } AsyncIO_rlimit_raiser;
}

AsyncIO::AsyncIO(class storage_pool &pool, monad::io::Buffers &rwbuf)
    : owning_tid_(get_tl_tid())
    , fds_{-1, -1}
    , uring_(rwbuf.ring())
    , wr_uring_(rwbuf.wr_ring())
    , rwbuf_(rwbuf)
    , rd_pool_(monad::io::BufferPool(rwbuf, true))
    , wr_pool_(monad::io::BufferPool(rwbuf, false))
{
    extant_write_operations_::init_header(&extant_write_operations_header_);
    if (wr_uring_ != nullptr) {
        // The write ring must have at least as many submission entries as there
        // are write i/o buffers
        auto const [sqes, cqes] = io_uring_ring_entries_left(true);
        MONAD_ASSERT_PRINTF(
            rwbuf.get_write_count() <= sqes,
            "rwbuf write count %zu sqes %u",
            rwbuf.get_write_count(),
            sqes);
    }

    auto &ts = detail::AsyncIO_per_thread_state();
    MONAD_ASSERT_PRINTF(
        ts.instance == nullptr,
        "currently cannot create more than one AsyncIO per thread at a time");
    ts.instance = this;

    // create and register the message type pipe for threadsafe communications
    // read side is nonblocking, write side is blocking
    auto *ring = const_cast<io_uring *>(&uring_.get_ring());
    if (!(ring->flags & IORING_SETUP_IOPOLL)) {
        MONAD_ASSERT_PRINTF(
            ::pipe2((int *)&fds_, O_NONBLOCK | O_DIRECT | O_CLOEXEC) != -1,
            "failed due to %s",
            strerror(errno));
        MONAD_ASSERT_PRINTF(
            ::fcntl(fds_.msgwrite, F_SETFL, O_DIRECT | O_CLOEXEC) != -1,
            "failed due to %s",
            strerror(errno));
        struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
        MONAD_ASSERT(sqe);
        io_uring_prep_poll_multishot(sqe, fds_.msgread, POLLIN);
        io_uring_sqe_set_data(
            sqe, detail::ASYNC_IO_MSG_PIPE_READY_IO_URING_DATA_MAGIC);
        MONAD_ASYNC_IO_URING_RETRYABLE(io_uring_submit(ring));
    }

    // TODO(niall): In the future don't activate all the chunks, as
    // theoretically zoned storage may enforce a maximum open zone count in
    // hardware. I cannot find any current zoned storage implementation that
    // does not implement infinite open zones so I went ahead and have been lazy
    // here, and we open everything all at once. It also means I can avoid
    // dynamic fd registration with io_uring, which simplifies implementation.
    storage_pool_ = &pool;
    cnv_chunk_ = std::static_pointer_cast<storage_pool::cnv_chunk>(
        pool.activate_chunk(storage_pool::cnv, 0));
    auto count = pool.chunks(storage_pool::seq);
    seq_chunks_.reserve(count);
    std::vector<int> fds;
    fds.reserve(count * 2 + 2);
    fds.push_back(cnv_chunk_.io_uring_read_fd);
    fds.push_back(cnv_chunk_.io_uring_write_fd);
    for (size_t n = 0; n < count; n++) {
        seq_chunks_.emplace_back(
            std::static_pointer_cast<storage_pool::seq_chunk>(
                pool.activate_chunk(
                    storage_pool::seq, static_cast<uint32_t>(n))));
        MONAD_ASSERT_PRINTF(
            seq_chunks_.back().ptr->capacity() >= MONAD_IO_BUFFERS_WRITE_SIZE,
            "sequential chunk capacity %llu must equal or exceed i/o buffer "
            "size %zu",
            seq_chunks_.back().ptr->capacity(),
            MONAD_IO_BUFFERS_WRITE_SIZE);
        MONAD_ASSERT(
            (seq_chunks_.back().ptr->capacity() %
             MONAD_IO_BUFFERS_WRITE_SIZE) == 0);
        fds.push_back(seq_chunks_[n].io_uring_read_fd);
        fds.push_back(seq_chunks_[n].io_uring_write_fd);
    }

    /* Annoyingly io_uring refuses duplicate file descriptors in its
    registration, and for efficiency the zoned storage emulation returns the
    same file descriptor for reads (and it may do so for writes depending). So
    reduce to a minimum mapped set.
    */
    unordered_dense_map<int, int> fd_to_iouring_map;
    for (auto fd : fds) {
        MONAD_ASSERT(fd != -1);
        fd_to_iouring_map[fd] = -1;
    }
    int idx = 0;
    fds.clear();
    for (auto &fd : fd_to_iouring_map) {
        fd.second = idx++;
        fds.push_back(fd.first);
    }
    // register files
    auto e = io_uring_register_files(
        const_cast<io_uring *>(&uring_.get_ring()),
        fds.data(),
        static_cast<unsigned int>(fds.size()));
    if (e) {
        fprintf(
            stderr,
            "io_uring_register_files with non-write ring failed due to %d %s\n",
            errno,
            strerror(errno));
    }
    MONAD_ASSERT(!e);
    if (wr_uring_ != nullptr) {
        e = io_uring_register_files(
            const_cast<io_uring *>(&wr_uring_->get_ring()),
            fds.data(),
            static_cast<unsigned int>(fds.size()));
        if (e) {
            fprintf(
                stderr,
                "io_uring_register_files with write ring failed due to %d "
                "%s\n",
                errno,
                strerror(errno));
        }
        MONAD_ASSERT(!e);
    }
    auto replace_fds_with_iouring_fds = [&](auto &p) {
        auto it = fd_to_iouring_map.find(p.io_uring_read_fd);
        MONAD_ASSERT(it != fd_to_iouring_map.end());
        p.io_uring_read_fd = it->second;
        it = fd_to_iouring_map.find(p.io_uring_write_fd);
        MONAD_ASSERT(it != fd_to_iouring_map.end());
        p.io_uring_write_fd = it->second;
    };
    replace_fds_with_iouring_fds(cnv_chunk_);
    for (auto &chnk : seq_chunks_) {
        replace_fds_with_iouring_fds(chnk);
    }
}

AsyncIO::~AsyncIO()
{
    wait_until_done();

    auto &ts = detail::AsyncIO_per_thread_state();
    MONAD_ASSERT_PRINTF(
        ts.instance == this,
        "this is being destructed not from its thread, bad idea");
    ts.instance = nullptr;

    if (wr_uring_ != nullptr) {
        MONAD_ASSERT(!io_uring_unregister_files(
            const_cast<io_uring *>(&wr_uring_->get_ring())));
    }
    MONAD_ASSERT(
        !io_uring_unregister_files(const_cast<io_uring *>(&uring_.get_ring())));

    ::close(fds_.msgread);
    ::close(fds_.msgwrite);
}

void AsyncIO::submit_request_(
    std::span<std::byte> buffer, chunk_offset_t chunk_and_offset,
    void *uring_data, enum erased_connected_operation::io_priority prio)
{
    MONAD_DEBUG_ASSERT(uring_data != nullptr);
    MONAD_DEBUG_ASSERT((chunk_and_offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
    MONAD_DEBUG_ASSERT(buffer.size() <= READ_BUFFER_SIZE);
#ifndef NDEBUG
    memset(buffer.data(), 0xff, buffer.size());
#endif

    poll_uring_while_submission_queue_full_();
    struct io_uring_sqe *sqe =
        io_uring_get_sqe(const_cast<io_uring *>(&uring_.get_ring()));
    MONAD_ASSERT(sqe);

    auto const &ci = seq_chunks_[chunk_and_offset.id];
    io_uring_prep_read_fixed(
        sqe,
        ci.io_uring_read_fd,
        buffer.data(),
        static_cast<unsigned int>(buffer.size()),
        ci.ptr->read_fd().second + chunk_and_offset.offset,
        0);
    sqe->flags |= IOSQE_FIXED_FILE;
    switch (prio) {
    case erased_connected_operation::io_priority::highest:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case erased_connected_operation::io_priority::idle:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    default:
        sqe->ioprio = 0;
        break;
    }

    io_uring_sqe_set_data(sqe, uring_data);
    MONAD_ASYNC_IO_URING_RETRYABLE(
        io_uring_submit(const_cast<io_uring *>(&uring_.get_ring())));
}

void AsyncIO::submit_request_(
    std::span<const struct iovec> buffers, chunk_offset_t chunk_and_offset,
    void *uring_data, enum erased_connected_operation::io_priority prio)
{
    MONAD_DEBUG_ASSERT(uring_data != nullptr);
    assert((chunk_and_offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
#ifndef NDEBUG
    for (auto const &buffer : buffers) {
        assert(buffer.iov_base != nullptr);
        memset(buffer.iov_base, 0xff, buffer.iov_len);
    }
#endif

    poll_uring_while_submission_queue_full_();
    struct io_uring_sqe *sqe =
        io_uring_get_sqe(const_cast<io_uring *>(&uring_.get_ring()));
    MONAD_ASSERT(sqe);

    auto const &ci = seq_chunks_[chunk_and_offset.id];
    if (buffers.size() == 1) {
        io_uring_prep_read(
            sqe,
            ci.io_uring_read_fd,
            buffers.front().iov_base,
            static_cast<unsigned int>(buffers.front().iov_len),
            ci.ptr->read_fd().second + chunk_and_offset.offset);
    }
    else {
        io_uring_prep_readv(
            sqe,
            ci.io_uring_read_fd,
            buffers.data(),
            static_cast<unsigned int>(buffers.size()),
            ci.ptr->read_fd().second + chunk_and_offset.offset);
    }
    sqe->flags |= IOSQE_FIXED_FILE;
    switch (prio) {
    case erased_connected_operation::io_priority::highest:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case erased_connected_operation::io_priority::idle:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    default:
        sqe->ioprio = 0;
        break;
    }

    io_uring_sqe_set_data(sqe, uring_data);
    MONAD_ASYNC_IO_URING_RETRYABLE(
        io_uring_submit(const_cast<io_uring *>(&uring_.get_ring())));
}

void AsyncIO::submit_request_(
    std::span<std::byte const> buffer, chunk_offset_t chunk_and_offset,
    void *uring_data, enum erased_connected_operation::io_priority prio)
{
    MONAD_DEBUG_ASSERT(uring_data != nullptr);
    MONAD_ASSERT(!rwbuf_.is_read_only());
    MONAD_DEBUG_ASSERT((chunk_and_offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
    MONAD_DEBUG_ASSERT(buffer.size() <= WRITE_BUFFER_SIZE);

    auto const &ci = seq_chunks_[chunk_and_offset.id];
    auto offset = ci.ptr->write_fd(buffer.size()).second;
    /* Do sanity check to ensure initiator is definitely appending where
    they are supposed to be appending.
    */
    MONAD_ASSERT_PRINTF(
        (chunk_and_offset.offset & 0xffff) == (offset & 0xffff),
        "where we are appending %u is not where we are supposed to be "
        "appending %llu. Chunk id is %u",
        (chunk_and_offset.offset & 0xffff),
        (offset & 0xffff),
        chunk_and_offset.id);

    auto *const wr_ring = (wr_uring_ != nullptr)
                              ? const_cast<io_uring *>(&wr_uring_->get_ring())
                              : const_cast<io_uring *>(&uring_.get_ring());
    struct io_uring_sqe *sqe = io_uring_get_sqe(wr_ring);
    MONAD_ASSERT(sqe);

    io_uring_prep_write_fixed(
        sqe,
        ci.io_uring_write_fd,
        buffer.data(),
        static_cast<unsigned int>(buffer.size()),
        offset,
        wr_ring == &uring_.get_ring());
    sqe->flags |= IOSQE_FIXED_FILE;
    if (wr_ring != &uring_.get_ring()) {
        sqe->flags |= IOSQE_IO_DRAIN;
    }
    // TODO(niall) test this to see if it helps prevent overwhelming the device
    // with writes
    // sqe->rw_flags |= RWF_DSYNC;
    switch (prio) {
    case erased_connected_operation::io_priority::highest:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_RT, 7);
        break;
    case erased_connected_operation::io_priority::idle:
        sqe->ioprio = IOPRIO_PRIO_VALUE(IOPRIO_CLASS_IDLE, 0);
        break;
    default:
        sqe->ioprio = 0;
        break;
    }

    io_uring_sqe_set_data(sqe, uring_data);
    MONAD_ASYNC_IO_URING_RETRYABLE(io_uring_submit(wr_ring));
}

void AsyncIO::poll_uring_while_submission_queue_full_()
{
    auto *ring = const_cast<io_uring *>(&uring_.get_ring());
    // if completions is getting close to full, drain some to prevent
    // completions getting dropped, which would break everything.
    auto const max_cq_entries =
        eager_completions_ ? 0 : (*ring->cq.kring_entries >> 1);
    while (io_uring_cq_ready(ring) > max_cq_entries) {
        if (!poll_uring_(false, 0)) {
            break;
        }
    }
    // block if no available sqe
    while (io_uring_sq_space_left(ring) == 0) {
        // Sleep the thread if there is i/o in flight, as a completion
        // will turn up at some point.
        //
        // Sometimes io_uring_sq_space_left can be zero at the same
        // time as there is no i/o in flight, in this situation don't
        // sleep waiting for completions which will never come.
        poll_uring_(io_in_flight() > 0, 0);
        // Rarely io_uring_sq_space_left stays stuck at zero, almost
        // as if the kernel thread went to sleep or disappeared. This
        // function doesn't do anything if io_uring_sq_space_left is
        // non zero, but if it remains zero then it uses a syscall to
        // give io_uring a poke.
        MONAD_ASSERT(io_uring_sqring_wait(ring) >= 0);
    }
}

// return the number of completions processed
// if blocking is true, will block until at least one completion is processed
size_t AsyncIO::poll_uring_(bool blocking, unsigned poll_rings_mask)
{
    // bit 0 in poll_rings_mask blocks read completions, bit 1 blocks write
    // completions
    MONAD_DEBUG_ASSERT((poll_rings_mask & 3) != 3);
    auto h = detail::AsyncIO_per_thread_state().enter_completions();
    MONAD_DEBUG_ASSERT(owning_tid_ == get_tl_tid());

    struct io_uring_cqe *cqe = nullptr;
    auto *const other_ring = const_cast<io_uring *>(&uring_.get_ring());
    auto *const wr_ring = (wr_uring_ != nullptr)
                              ? const_cast<io_uring *>(&wr_uring_->get_ring())
                              : nullptr;
    auto dequeue_concurrent_read_ios_pending = [&]() {
        if (concurrent_read_io_limit_ > 0) {
            auto const max_cq_entries =
                eager_completions_ ? 0 : (*other_ring->cq.kring_entries >> 1);
            for (auto *state = concurrent_read_ios_pending_.first;
                 state != nullptr;
                 state = concurrent_read_ios_pending_.first) {
                if (records_.inflight_rd >= concurrent_read_io_limit_ ||
                    io_uring_sq_space_left(other_ring) == 0 ||
                    io_uring_cq_ready(other_ring) > max_cq_entries) {
                    break;
                }
                auto *next =
                    erased_connected_operation::rbtree_node_traits::get_right(
                        state);
                if (next == nullptr) {
                    MONAD_DEBUG_ASSERT(concurrent_read_ios_pending_.count == 1);
                    concurrent_read_ios_pending_.first =
                        concurrent_read_ios_pending_.last = nullptr;
                }
                else {
                    concurrent_read_ios_pending_.first = next;
                }
                concurrent_read_ios_pending_.count--;
                state->reinitiate();
            }
        }
    };
    dequeue_concurrent_read_ios_pending();

    io_uring *ring = nullptr;
    erased_connected_operation *state = nullptr;
    result<size_t> res(success(0));
    auto get_cqe = [&] {
        auto const inflight_ts =
            records_.inflight_ts.load(std::memory_order_acquire);

        if (wr_ring != nullptr && records_.inflight_wr > 0 &&
            (poll_rings_mask & 2) == 0) {
            ring = wr_ring;
            if (wr_uring_->must_call_uring_submit() ||
                !!(wr_ring->flags & IORING_SETUP_IOPOLL)) {
                // If i/o polling is on, but there is no kernel thread to do the
                // polling for us OR the kernel thread has gone to sleep, we
                // need to call the io_uring_enter syscall from userspace to do
                // the completions processing. From studying the liburing source
                // code, this will do it.
                MONAD_ASYNC_IO_URING_RETRYABLE(io_uring_submit(wr_ring));
            }
            io_uring_peek_cqe(wr_ring, &cqe);
            if ((poll_rings_mask & 1) != 0) {
                if (blocking && inflight_ts == 0 &&
                    detail::AsyncIO_per_thread_state().empty()) {
                    MONAD_ASYNC_IO_URING_RETRYABLE(
                        io_uring_wait_cqe(ring, &cqe));
                }
                if (cqe == nullptr) {
                    return false;
                }
            }
        }
        if (cqe == nullptr) {
            ring = other_ring;
            if (uring_.must_call_uring_submit() ||
                !!(other_ring->flags & IORING_SETUP_IOPOLL)) {
                // If i/o polling is on, but there is no kernel thread to do the
                // polling for us OR the kernel thread has gone to sleep, we
                // need to call the io_uring_enter syscall from userspace to do
                // the completions processing. From studying the liburing source
                // code, this will do it.
                MONAD_ASYNC_IO_URING_RETRYABLE(io_uring_submit(other_ring));
            }
            if (blocking && inflight_ts == 0 && records_.inflight_wr == 0 &&
                detail::AsyncIO_per_thread_state().empty()) {
                MONAD_ASYNC_IO_URING_RETRYABLE(io_uring_wait_cqe(ring, &cqe));
            }
            else {
                // If nothing in io_uring and there are no threadsafe ops in
                // flight, return false
                if (0 != io_uring_peek_cqe(ring, &cqe) && inflight_ts == 0) {
                    return false;
                }
            }
        }

        void *data = (cqe != nullptr)
                         ? io_uring_cqe_get_data(cqe)
                         : detail::ASYNC_IO_MSG_PIPE_READY_IO_URING_DATA_MAGIC;
        MONAD_ASSERT(data);
        if (data == detail::ASYNC_IO_MSG_PIPE_READY_IO_URING_DATA_MAGIC) {
            // MSG_READ pipe has a message for us. It is simply the pointer to
            // the connected operation state for us to complete.
            MONAD_ASSERT(cqe == nullptr || cqe->res == POLLIN);
            if (cqe != nullptr && !(cqe->flags & IORING_CQE_F_MORE)) {
                // Rearm the poll
                struct io_uring_sqe *sqe = io_uring_get_sqe(ring);
                MONAD_ASSERT(sqe);
                io_uring_prep_poll_multishot(sqe, fds_.msgread, POLLIN);
                io_uring_sqe_set_data(
                    sqe, detail::ASYNC_IO_MSG_PIPE_READY_IO_URING_DATA_MAGIC);
                MONAD_ASYNC_IO_URING_RETRYABLE(io_uring_submit(ring));
            }
            auto readed = ::read(
                fds_.msgread, &state, sizeof(erased_connected_operation *));
            if (readed >= 0) {
                MONAD_ASSERT(sizeof(erased_connected_operation *) == readed);
                // Writes flushed in the submitting thread must be acquired now
                // before state can be dereferenced
                std::atomic_thread_fence(std::memory_order_acquire);
            }
            else {
                if (EAGAIN == errno || EWOULDBLOCK == errno) {
                    // Spurious wakeup
                    if (cqe != nullptr) {
                        io_uring_cqe_seen(ring, cqe);
                        cqe = nullptr;
                    }
                    return true;
                }
                else {
                    MONAD_ASSERT(readed >= 0);
                }
            }
        }
        else {
            state = reinterpret_cast<erased_connected_operation *>(data);
            res = (cqe->res < 0) ? result<size_t>(posix_code(-cqe->res))
                                 : result<size_t>(cqe->res);
        }
        if (cqe != nullptr) {
            io_uring_cqe_seen(ring, cqe);
            cqe = nullptr;
        }

        if (capture_io_latencies_) {
            state->elapsed =
                std::chrono::steady_clock::now() - state->initiated;
        }
        return true;
    };

    auto process_cqe = [&] {
        // For now, only silently retry reads and scatter reads
        auto retry_operation_if_temporary_failure = [&] {
            [[unlikely]] if (
                res.has_error() &&
                res.assume_error() == errc::resource_unavailable_try_again) {
                records_.reads_retried++;
                /* This is what the io_uring source code does when
                EAGAIN comes back in a cqe and the submission queue
                is full. It effectively is a "hard pace", and given how
                rare EAGAIN is, it's probably not a bad idea to truly
                slow things down if it occurs.
                */
                while (io_uring_sq_space_left(ring) == 0) {
                    ::usleep(50);
                    MONAD_ASSERT(io_uring_sqring_wait(ring) >= 0);
                }
                state->reinitiate();
                return true;
            }
            return false;
        };
        bool is_read_or_write = false;
        if (state->is_read()) {
            --records_.inflight_rd;
            is_read_or_write = true;
            if (retry_operation_if_temporary_failure()) {
                return true;
            }
            // Speculative read i/o deque
            dequeue_concurrent_read_ios_pending();
        }
        else if (state->is_write()) {
            --records_.inflight_wr;
            is_read_or_write = true;
        }
        else if (state->is_timeout()) {
            --records_.inflight_tm;
        }
        else if (state->is_threadsafeop()) {
            records_.inflight_ts.fetch_sub(1, std::memory_order_acq_rel);
        }
        else if (state->is_read_scatter()) {
            --records_.inflight_rd_scatter;
            if (retry_operation_if_temporary_failure()) {
                return true;
            }
        }
#ifndef NDEBUG
        else {
            abort();
        }
#endif
        erased_connected_operation_unique_ptr_type h2;
        std::unique_ptr<erased_connected_operation> h3;
        if (state->lifetime_is_managed_internally()) {
            if (is_read_or_write) {
                h2 = erased_connected_operation_unique_ptr_type{state};
            }
            else {
                h3 = std::unique_ptr<erased_connected_operation>(state);
            }
        }
        state->completed(std::move(res));
        return true;
    };
    if (!eager_completions_) {
        auto ret = get_cqe();
        if (state == nullptr) {
            return ret;
        }
        return static_cast<size_t>(process_cqe());
    }

    // eager completions mode, drain everything possible
    struct completion_t
    {
        io_uring *ring{nullptr};
        erased_connected_operation *state{nullptr};
        result<size_t> res{success(0)};
    };

    std::vector<completion_t> completions;
    completions.reserve(
        2 + io_uring_sq_ready(other_ring) +
        ((wr_ring != nullptr) ? io_uring_sq_ready(wr_ring) : 0));
    for (;;) {
        ring = nullptr;
        state = nullptr;
        res = 0;
        get_cqe();
        if (state == nullptr) {
            break;
        }
        completions.emplace_back(ring, state, std::move(res));
        blocking = false;
    }
    for (auto &i : completions) {
        ring = i.ring;
        state = i.state;
        res = std::move(i.res);
        process_cqe();
    }
    return completions.size();
}

unsigned AsyncIO::deferred_initiations_in_flight() const noexcept
{
    auto &ts = detail::AsyncIO_per_thread_state();
    return !ts.empty() && !ts.am_within_completions();
}

std::pair<unsigned, unsigned>
AsyncIO::io_uring_ring_entries_left(bool for_wr_ring) const noexcept
{
    if (for_wr_ring) {
        if (wr_uring_ == nullptr) {
            return {0, 0};
        }
        auto *ring = const_cast<io_uring *>(&wr_uring_->get_ring());
        return {
            io_uring_sq_space_left(ring),
            *ring->cq.kring_entries - io_uring_cq_ready(ring)};
    }
    auto *ring = const_cast<io_uring *>(&uring_.get_ring());
    return {
        io_uring_sq_space_left(ring),
        *ring->cq.kring_entries - io_uring_cq_ready(ring)};
}

void AsyncIO::dump_fd_to(size_t which, std::filesystem::path const &path)
{
    int const tofd = ::creat(path.c_str(), 0600);
    MONAD_ASSERT_PRINTF(tofd != -1, "creat failed due to %s", strerror(errno));
    auto untodfd = make_scope_exit([tofd]() noexcept { ::close(tofd); });
    auto fromfd = seq_chunks_[which].ptr->read_fd();
    MONAD_ASSERT(fromfd.second <= std::numeric_limits<off64_t>::max());
    off64_t off_in = static_cast<off64_t>(fromfd.second);
    off64_t off_out = 0;
    auto copied = copy_file_range(
        fromfd.first,
        &off_in,
        tofd,
        &off_out,
        seq_chunks_[which].ptr->size(),
        0);
    MONAD_ASSERT_PRINTF(
        copied != -1, "copy_file_range failed due to %s", strerror(errno));
}

unsigned char *AsyncIO::poll_uring_while_no_io_buffers_(bool is_write)
{
    /* Prevent any new i/o initiation as we cannot exit until an i/o
    buffer becomes freed.
    */
    auto h = detail::AsyncIO_per_thread_state().enter_completions();
    for (;;) {
        // If this assert fails, there genuinely
        // are not enough i/o buffers. This can happen if the caller
        // initiates more i/o than there are buffers available.
        if (0 == io_in_flight()) {
            std::cerr
                << "FATAL: no i/o buffers remaining. is_write = " << is_write
                << " within_completions_count = "
                << detail::AsyncIO_per_thread_state().within_completions_count
                << std::endl;
            MONAD_ABORT("no i/o buffers remaining");
        }
        // Reap completions until a buffer frees up, only reaping completions
        // for the write or other ring exclusively.
        poll_uring_(true, is_write ? 1 : 2);
        auto *mem = (is_write ? wr_pool_ : rd_pool_).alloc();
        if (mem != nullptr) {
            return mem;
        }
    }
}

MONAD_ASYNC_NAMESPACE_END
