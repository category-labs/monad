#include <boost/outcome/utils.hpp>
#include <monad/async/io.hpp>

#include <monad/async/concepts.hpp>
#include <monad/async/config.h>
#include <monad/async/config.hpp>
#include <monad/async/context_switcher.h>
#include <monad/async/cpp_helpers.hpp>
#include <monad/async/detail/connected_operation_storage.hpp>
#include <monad/async/detail/scope_polyfill.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <monad/async/executor.h>
#include <monad/async/file_io.h>
#include <monad/async/storage_pool.hpp>
#include <monad/async/task.h>
#include <monad/core/assert.h>
#include <monad/core/unordered_map.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>

#include <atomic>
#include <cassert>
#include <cerrno>
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
#include <system_error>
#include <type_traits>
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

MONAD_ASYNC_NAMESPACE_BEGIN

namespace detail
{
    // diseased dead beef in hex, last bit set so won't be a pointer
    // static void *const ASYNC_IO_MSG_PIPE_READY_IO_URING_DATA_MAGIC =
    //    (void *)(uintptr_t)0xd15ea5eddeadbeef;

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
#ifndef NDEBUG
        std::set<int> fd_reservation;
#endif
        AsyncIO_rlimit_raiser_impl()
        {
            size_t n = 4096;
            for (; n >= 1024; n >>= 1) {
                struct rlimit const r{n, n};
                int const ret = setrlimit(RLIMIT_NOFILE, &r);
                if (ret >= 0) {
                    break;
                }
            }
            if (n < 4096) {
                std::cerr << "WARNING: maximum hard file descriptor kimit is "
                          << n
                          << " which is less than 4096. 'Too many open files' "
                             "errors may result. You can increase the hard "
                             "file descriptor limit for a given user by adding "
                             "to '/etc/security/limits.conf' '<username> hard "
                             "nofile 16384'."
                          << std::endl;
            }
#ifndef NDEBUG
            /* If in debug, reserve the first 1024 file descriptor numbers
            in order to better reveal software which is not >= 1024 fd number
            safe, which is still some third party dependencies on Linux. */
            else {
                for (int fd = ::dup(0); fd > 0 && fd < 1024; fd = ::dup(0)) {
                    fd_reservation.insert(fd);
                }
            }
#endif
        }

        ~AsyncIO_rlimit_raiser_impl()
        {
#ifndef NDEBUG
            while (!fd_reservation.empty()) {
                (void)::close(*fd_reservation.begin());
                fd_reservation.erase(fd_reservation.begin());
            }
#endif
        }
    } AsyncIO_rlimit_raiser;

}

AsyncIO::AsyncIO(class storage_pool &pool, monad::io::Buffers &rwbuf)
    : executor_attr_{}
    , owning_tid_(gettid())
{
    extant_write_operations_::init_header(&extant_write_operations_header_);
    /* Temporarily we shall simply clone config into the new i/o executor from
    rwbuf. At some future point we will do all the refactoring to remove clients
    configuring io_uring manually.
    */
    executor_attr_.io_uring_ring.entries = rwbuf.ring().get_sq_entries();
    executor_attr_.io_uring_ring.params.flags = rwbuf.ring().get_ring().flags;
    executor_attr_.io_uring_ring.registered_buffers.small_count =
        (unsigned)rwbuf.get_read_count();
    executor_attr_.io_uring_ring.registered_buffers.small_multiplier =
        (unsigned)rwbuf.get_read_size() / 4096;
    if (rwbuf.wr_ring() != nullptr) {
        executor_attr_.io_uring_wr_ring.entries =
            rwbuf.wr_ring()->get_sq_entries();
        executor_attr_.io_uring_wr_ring.params.flags =
            rwbuf.wr_ring()->get_ring().flags;
        executor_attr_.io_uring_wr_ring.registered_buffers.large_count =
            (unsigned)rwbuf.get_write_count();
        executor_attr_.io_uring_wr_ring.registered_buffers.large_multiplier =
            (unsigned)rwbuf.get_write_size() / (2 * 1024 * 1024);
    }
    executor_ = monad::async::make_executor(executor_attr_);
    context_switcher_ =
        monad::async::make_context_switcher(monad_async_context_switcher_sjlj);
    monad_async_task_attr task_attr{};
    dispatch_task_ =
        monad::async::make_task(context_switcher_.get(), task_attr);
    dispatch_task_->user_code = &AsyncIO::dispatch_task_impl_;
    dispatch_task_->user_ptr = (void *)this;
    to_result(
        monad_async_task_attach(executor_.get(), dispatch_task_.get(), nullptr))
        .value();

    auto &ts = detail::AsyncIO_per_thread_state();
    MONAD_ASSERT(ts.instance == nullptr); // currently cannot create more than
                                          // one AsyncIO per thread at a time
    ts.instance = this;

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
    fds.push_back(cnv_chunk_.read_fd);
    fds.push_back(cnv_chunk_.write_fd);
    for (size_t n = 0; n < count; n++) {
        seq_chunks_.emplace_back(
            std::static_pointer_cast<storage_pool::seq_chunk>(
                pool.activate_chunk(
                    storage_pool::seq, static_cast<uint32_t>(n))));
        MONAD_ASSERT(
            seq_chunks_.back().ptr->capacity() >= MONAD_IO_BUFFERS_WRITE_SIZE);
        MONAD_ASSERT(
            (seq_chunks_.back().ptr->capacity() %
             MONAD_IO_BUFFERS_WRITE_SIZE) == 0);
        fds.push_back(seq_chunks_[n].read_fd);
        fds.push_back(seq_chunks_[n].write_fd);
    }

    auto &h = launch_on_task_from_pool_(
        [&](monad_async_task task) -> result<intptr_t> {
            try {
                /* io_uring refuses duplicate file descriptors in its
                registration, and for efficiency the zoned storage emulation
                returns the same file descriptor for reads (and it may do so for
                writes depending). So reduce to a minimum mapped set.
                */
                unordered_dense_map<
                    int,
                    std::shared_ptr<monad::async::file_ptr::element_type>>
                    fd_to_iouring_map;
                for (auto fd : fds) {
                    MONAD_ASSERT(fd != -1);
                    fd_to_iouring_map[fd] = nullptr;
                }
                fds.clear();
                for (auto &fd : fd_to_iouring_map) {
                    monad_async_file file;
                    monad::async::to_result(
                        monad_async_task_file_create_from_existing_fd(
                            &file, task, fd.first))
                        .value();
                    fd.second =
                        std::shared_ptr<monad::async::file_ptr::element_type>(
                            file_ptr(file, file_deleter(executor_.get())));
                    fds.push_back(fd.first);
                }
                auto replace_fds_with_iouring_fds = [&](auto &p) {
                    auto it = fd_to_iouring_map.find(p.read_fd);
                    MONAD_ASSERT(it != fd_to_iouring_map.end());
                    p.io_uring_read_fd = it->second;
                    it = fd_to_iouring_map.find(p.write_fd);
                    MONAD_ASSERT(it != fd_to_iouring_map.end());
                    p.io_uring_write_fd = it->second;
                };
                replace_fds_with_iouring_fds(cnv_chunk_);
                for (auto &chnk : seq_chunks_) {
                    replace_fds_with_iouring_fds(chnk);
                }
                return success(0);
            }
            catch (...) {
                return system_code_from_exception();
            }
        });
    do {
        to_result(
            monad_async_executor_run(executor_.get(), (size_t)-1, nullptr))
            .value();
    }
    while (h.second);

    // Warm up the task pool
    for (size_t n = 0; n < 1024; n++) {
        launch_on_task_from_pool_(
            [&](monad_async_task) -> result<intptr_t> { return success(0); });
    }
    to_result(monad_async_executor_run(executor_.get(), (size_t)-1, nullptr))
        .value();
}

AsyncIO::~AsyncIO()
{
    wait_until_done();
#if 0
    struct timespec nowait
    {
        .tv_sec = 0, .tv_nsec = 0
    };

    auto r = to_result(
        monad_async_executor_run(executor_.get(), size_t(-1), &nowait));
    if (!r && r.assume_error() != errc::stream_timeout) {
        r.value();
    }
#endif
    if (task_pool_sleeping_.size() > 1024) {
        std::cout << "NOTE: AsyncIO Peak tasks was "
                  << task_pool_sleeping_.size() << std::endl;
    }

    auto &ts = detail::AsyncIO_per_thread_state();
    MONAD_ASSERT(
        ts.instance ==
        this); // this is being destructed not from its thread, bad idea
    ts.instance = nullptr;

    // Cancel the dispatch task
    {
        auto &h = launch_on_task_from_pool_(
            [&](monad_async_task) -> result<intptr_t> {
                (void)to_result(monad_async_task_cancel(
                    executor_.get(), dispatch_task_.get()));
                return success(0);
            });
        do {
            to_result(monad_async_executor_run(executor_.get(), 1, nullptr))
                .value();
        }
        while (h.second || !monad_async_task_has_exited(dispatch_task_.get()));
    }

    // File handles need to be closed by a task, not by main thread
    {
        auto &h = launch_on_task_from_pool_(
            [&](monad_async_task) -> result<intptr_t> {
                seq_chunks_.clear();
                cnv_chunk_.io_uring_read_fd.reset();
                cnv_chunk_.io_uring_write_fd.reset();
                return success(0);
            });
        do {
            to_result(monad_async_executor_run(executor_.get(), 1, nullptr))
                .value();
        }
        while (h.second);
    }
}

template <class U>
    requires(std::is_invocable_v<U>)
void AsyncIO::submit_request_within_task_(U &&f, bool force_launch_on_pool)
{
    MONAD_ASSERT(dispatch_task_);
    MONAD_ASSERT(!monad_async_task_has_exited(dispatch_task_.get()));
    auto *task = executor_->current_task.load(std::memory_order_acquire);
    if (force_launch_on_pool || task == nullptr) {
        launch_on_task_from_pool_(
            [this, f = std::move(f)](
                monad_async_task task) mutable -> result<intptr_t> {
                try {
                    // All i/o initiated should complete on the dispatcher
                    // task
                    task->io_recipient_task = dispatch_task_.get();
                    f();
                    return success();
                }
                catch (...) {
                    return system_code_from_exception();
                }
            });
    }
    else if (task->is_running.load(std::memory_order_acquire)) {
        f();
    }
    else {
        /* The task is neither currently running nor is exited, this is
         usually due to multiple concurrent timeout ops being submitted.
         */
        MONAD_ASSERT(false);
    }
}

void AsyncIO::submit_request_(
    std::span<std::byte> buffer, chunk_offset_t chunk_and_offset,
    void *uring_data, enum erased_connected_operation::io_priority prio)
{
    submit_request_within_task_([=, this] {
        MONAD_DEBUG_ASSERT(uring_data != nullptr);
        MONAD_DEBUG_ASSERT(
            (chunk_and_offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
        MONAD_DEBUG_ASSERT(buffer.size() <= READ_BUFFER_SIZE);
#ifndef NDEBUG
        memset(buffer.data(), 0xff, buffer.size());
#endif

        auto const &ci = seq_chunks_[chunk_and_offset.id];
        struct iovec vec[] = {{(void *)buffer.data(), buffer.size()}};
        auto *task = executor_->current_task.load(std::memory_order_acquire);
        auto oldprio = task->priority.io;
        switch (prio) {
        case erased_connected_operation::io_priority::highest:
            to_result(monad_async_task_set_priorities(
                          task,
                          monad_async_priority_unchanged,
                          monad_async_priority_high))
                .value();
            break;
        case erased_connected_operation::io_priority::idle:
            to_result(monad_async_task_set_priorities(
                          task,
                          monad_async_priority_unchanged,
                          monad_async_priority_low))
                .value();
            break;
        default:
            break;
        }
        monad_async_task_file_read(
            ((erased_connected_operation *)uring_data)->to_iostatus(),
            task,
            ci.io_uring_read_fd.get(),
            0 /*fixme use registered buffer ids*/,
            vec,
            1,
            ci.ptr->read_fd().second + chunk_and_offset.offset,
            0);
        if (task->priority.io != oldprio) {
            to_result(monad_async_task_set_priorities(
                          task, monad_async_priority_unchanged, oldprio))
                .value();
        }
    });
}

void AsyncIO::submit_request_(
    std::span<const struct iovec> buffers, chunk_offset_t chunk_and_offset,
    void *uring_data, enum erased_connected_operation::io_priority prio)
{
    submit_request_within_task_([=, this] {
        MONAD_DEBUG_ASSERT(uring_data != nullptr);
        assert((chunk_and_offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
#ifndef NDEBUG
        for (auto const &buffer : buffers) {
            assert(buffer.iov_base != nullptr);
            memset(buffer.iov_base, 0xff, buffer.iov_len);
        }
#endif

        auto const &ci = seq_chunks_[chunk_and_offset.id];
        auto *task = executor_->current_task.load(std::memory_order_acquire);
        auto oldprio = task->priority.io;
        switch (prio) {
        case erased_connected_operation::io_priority::highest:
            to_result(monad_async_task_set_priorities(
                          task,
                          monad_async_priority_unchanged,
                          monad_async_priority_high))
                .value();
            break;
        case erased_connected_operation::io_priority::idle:
            to_result(monad_async_task_set_priorities(
                          task,
                          monad_async_priority_unchanged,
                          monad_async_priority_low))
                .value();
            break;
        default:
            break;
        }
        monad_async_task_file_read(
            ((erased_connected_operation *)uring_data)->to_iostatus(),
            task,
            ci.io_uring_read_fd.get(),
            0 /*fixme use registered buffer ids*/,
            buffers.data(),
            (unsigned)buffers.size(),
            ci.ptr->read_fd().second + chunk_and_offset.offset,
            0);
        if (task->priority.io != oldprio) {
            to_result(monad_async_task_set_priorities(
                          task, monad_async_priority_unchanged, oldprio))
                .value();
        }
    });
}

void AsyncIO::submit_request_(
    std::span<std::byte const> buffer, chunk_offset_t chunk_and_offset,
    void *uring_data, enum erased_connected_operation::io_priority prio)
{
    submit_request_within_task_([=, this] {
        MONAD_DEBUG_ASSERT(uring_data != nullptr);
        MONAD_DEBUG_ASSERT(
            (chunk_and_offset.offset & (DISK_PAGE_SIZE - 1)) == 0);
        MONAD_DEBUG_ASSERT(buffer.size() <= WRITE_BUFFER_SIZE);

        auto const &ci = seq_chunks_[chunk_and_offset.id];
        auto offset = ci.ptr->write_fd(buffer.size()).second;
        /* Do sanity check to ensure initiator is definitely appending where
        they are supposed to be appending.
        */
        MONAD_ASSERT((chunk_and_offset.offset & 0xffff) == (offset & 0xffff));

        struct iovec vec[] = {{(void *)buffer.data(), buffer.size()}};
        auto *task = executor_->current_task.load(std::memory_order_acquire);
        auto oldprio = task->priority.io;
        switch (prio) {
        case erased_connected_operation::io_priority::highest:
            to_result(monad_async_task_set_priorities(
                          task,
                          monad_async_priority_unchanged,
                          monad_async_priority_high))
                .value();
            break;
        case erased_connected_operation::io_priority::idle:
            to_result(monad_async_task_set_priorities(
                          task,
                          monad_async_priority_unchanged,
                          monad_async_priority_low))
                .value();
            break;
        default:
            break;
        }
        monad_async_task_file_write(
            ((erased_connected_operation *)uring_data)->to_iostatus(),
            task,
            ci.io_uring_write_fd.get(),
            0 /*fixme use registered buffer ids*/,
            vec,
            1,
            ci.ptr->read_fd().second + chunk_and_offset.offset,
            0);
        if (task->priority.io != oldprio) {
            to_result(monad_async_task_set_priorities(
                          task, monad_async_priority_unchanged, oldprio))
                .value();
        }
    });
}

void AsyncIO::submit_request_(timed_invocation_state *state, void *uring_data)
{
    submit_request_within_task_(
        [=, this] {
            MONAD_DEBUG_ASSERT(uring_data != nullptr);
            MONAD_DEBUG_ASSERT(
                !state->timespec_is_absolute); // not implemented yet
            MONAD_DEBUG_ASSERT(
                !state->timespec_is_utc_clock); // not implemented yet
            uint64_t ns =
                (uint64_t)(state->ts.tv_sec * 1000000000LL + state->ts.tv_nsec);
            auto *task =
                executor_->current_task.load(std::memory_order_acquire);
            to_result(monad_async_task_suspend_for_duration(nullptr, task, ns))
                .value();
            // auto h =
            // detail::AsyncIO_per_thread_state().enter_completions();
            ((erased_connected_operation *)uring_data)->completed(success());
            --records_.inflight_tm;
        },
        true);
}

void AsyncIO::invoke_completed_(
    erased_connected_operation *state, result<size_t> res)
{
    if (state->is_read()) {
        --records_.inflight_rd;
    }
    else if (state->is_write()) {
        --records_.inflight_wr;
    }
    else if (state->is_timeout()) {
        --records_.inflight_tm;
    }
    else if (state->is_threadsafeop()) {
        records_.inflight_ts.fetch_sub(1, std::memory_order_acq_rel);
    }
    else if (state->is_read_scatter()) {
        --records_.inflight_rd_scatter;
    }
#ifndef NDEBUG
    else {
        abort();
    }
#endif
    erased_connected_operation_unique_ptr_type h2;
    std::unique_ptr<erased_connected_operation> h3;
    if (state->lifetime_is_managed_internally()) {
        if (state->is_read() || state->is_write()) {
            h2 = erased_connected_operation_unique_ptr_type{state};
        }
        else {
            h3 = std::unique_ptr<erased_connected_operation>(state);
        }
    }
    // auto h = detail::AsyncIO_per_thread_state().enter_completions();
    state->completed(std::move(res));
}

monad_async_result AsyncIO::dispatch_task_impl_(monad_async_task task) noexcept
{
    auto *self = (AsyncIO *)task->user_ptr;
    bool have_been_cancelled = false;
    for (;;) {
        monad_async_io_status *completed = nullptr;
        auto io_to_be_reaped =
            to_result(monad_async_task_suspend_until_completed_io(
                &completed, task, monad_async_duration_infinite_cancelling));
        if (!io_to_be_reaped) {
            if (io_to_be_reaped.assume_error() == errc::operation_canceled) {
                return monad_async_make_success(0);
            }
            io_to_be_reaped.value();
        }
        if (completed != nullptr) {
            auto *state = erased_connected_operation::from_iostatus(completed);
            result<size_t> res(to_result(completed->result));
            // This dispatch task must never do anything but dispatching, so
            // invoke completion on the pool.
            self->submit_request_within_task_(
                [self, state, res = std::move(res)]() mutable {
                    self->invoke_completed_(state, std::move(res));
                },
                true);
        }
        if (io_to_be_reaped.assume_value() < 2) {
            if (have_been_cancelled) {
                return monad_async_make_success(0);
            }
            auto r = to_result(monad_async_task_suspend_for_duration(
                &completed, task, monad_async_duration_infinite_cancelling));
            if (!r) {
                if (r.assume_error() == errc::operation_canceled) {
                    have_been_cancelled = true;
                    continue;
                }
                r.value();
            }
        }
    }
}

bool AsyncIO::poll_uring_(bool blocking)
{
    MONAD_DEBUG_ASSERT(owning_tid_ == gettid());
    if (dispatch_task_->io_submitted == 0 &&
        dispatch_task_->io_completed_not_reaped == 0) {
        blocking = false;
    }
    MONAD_ASSERT(!monad_async_task_has_exited(dispatch_task_.get()));
    if (executor_->current_task.load(std::memory_order_acquire) != nullptr) {
        // We are within a task already, cannot reenter the executor so do
        // nothing.
        return false;
    }
    auto h = detail::AsyncIO_per_thread_state().enter_completions();

    struct timespec nowait
    {
        0, 0
    };

    erased_connected_operation *threadsafe_invocation = nullptr;
    std::unique_lock g(threadsafe_invocations_lock_);
    if (!threadsafe_invocations_.empty()) {
        threadsafe_invocation = threadsafe_invocations_.front();
        threadsafe_invocations_.pop_front();
    }
    g.unlock();
    if (threadsafe_invocation != nullptr) {
        // Invoke completion on the pool.
        submit_request_within_task_(
            [this, threadsafe_invocation]() mutable {
                invoke_completed_(threadsafe_invocation, success());
            },
            true);
        blocking = false;
    }
    auto r = to_result(monad_async_executor_run(
        executor_.get(), 1, blocking ? nullptr : &nowait));
    if (!r) {
        if (r.assume_error() != errc::stream_timeout &&
            r.assume_error() != errc::interrupted) {
            r.value();
        }
        r = success(0);
    }
    return r.assume_value() > 0 || threadsafe_invocation != nullptr;
}

unsigned AsyncIO::deferred_initiations_in_flight() const noexcept
{
    auto &ts = detail::AsyncIO_per_thread_state();
    auto tasks_suspended =
        (unsigned)executor_->tasks_suspended.load(std::memory_order_acquire);
    if (dispatch_task_ && !monad_async_task_has_exited(dispatch_task_.get())) {
        tasks_suspended--;
    }
    return (!ts.empty() && !ts.am_within_completions()) +
           (unsigned)executor_->tasks_pending_launch.load(
               std::memory_order_acquire) +
           tasks_suspended +
           (unsigned)executor_->tasks_suspended_sqe_exhaustion.load(
               std::memory_order_acquire);
}

void AsyncIO::dump_fd_to(size_t which, std::filesystem::path const &path)
{
    int const tofd = ::creat(path.c_str(), 0600);
    if (tofd == -1) {
        throw std::system_error(std::error_code(errno, std::system_category()));
    }
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
    if (copied == -1) {
        throw std::system_error(std::error_code(errno, std::system_category()));
    }
}

void AsyncIO::submit_threadsafe_invocation_request(
    erased_connected_operation *uring_data)
{
    // WARNING: This function is usually called from foreign kernel threads!
    records_.inflight_ts.fetch_add(1, std::memory_order_acq_rel);
    std::unique_lock g(threadsafe_invocations_lock_);
    threadsafe_invocations_.push_back(uring_data);
    auto res = monad_async_make_failure(EINTR);
    to_result(monad_async_executor_wake(executor_.get(), &res)).value();
    g.unlock();
}

monad_async_task_registered_io_buffer
AsyncIO::poll_uring_while_no_io_buffers_(bool is_write)
{
    // If we are here, we are not running within a task by definition.
    MONAD_DEBUG_ASSERT(
        executor_->current_task.load(std::memory_order_acquire) == nullptr);

    monad_async_task_registered_io_buffer buffer{};
    auto &h = launch_on_task_from_pool_(
        [&](monad_async_task task) -> result<intptr_t> {
            monad::async::to_result(
                monad_async_task_claim_registered_io_buffer(
                    &buffer,
                    task,
                    is_write ? WRITE_BUFFER_SIZE : READ_BUFFER_SIZE,
                    {.for_write_ring = is_write, .fail_dont_suspend = false}))
                .value();
            return success();
        });
    /* Prevent any new i/o initiation as we cannot exit until an i/o
    buffer becomes freed.
    */
    auto h2 = detail::AsyncIO_per_thread_state().enter_completions();
    while (h.second) {
        poll_uring_(true);
    }
    return buffer;
}

MONAD_ASYNC_NAMESPACE_END
