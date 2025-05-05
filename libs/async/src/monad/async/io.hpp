#pragma once

#include <monad/async/connected_operation.hpp>

#include <monad/async/storage_pool.hpp>

#include <monad/io/buffer_pool.hpp>
#include <monad/io/buffers.hpp>
#include <monad/io/ring.hpp>

#include <monad/mem/allocators.hpp>

#include <atomic>
#include <cassert>
#include <concepts>
#include <cstddef>
#include <filesystem>
#include <functional>
#include <iostream>
#include <span>
#include <tuple>

MONAD_ASYNC_NAMESPACE_BEGIN

class read_single_buffer_sender;

// helper struct that records IO stats
struct IORecord
{
    unsigned inflight_rd{0};
    unsigned inflight_rd_scatter{0};
    unsigned inflight_wr{0};
    unsigned inflight_tm{0};
    std::atomic<unsigned> inflight_ts{0};

    unsigned max_inflight_rd{0};
    unsigned max_inflight_rd_scatter{0};
    unsigned max_inflight_wr{0};

    unsigned nreads{0};
    // Reads and scatter reads which got a EAGAIN and were retried
    unsigned reads_retried{0};
};

class AsyncIO final
{
public:
    struct timed_invocation_state;

private:
    friend class read_single_buffer_sender;
    using _storage_pool = class storage_pool;
    using cnv_chunk = _storage_pool::cnv_chunk;
    using seq_chunk = _storage_pool::seq_chunk;

    template <class T>
    struct chunk_ptr_
    {
        std::shared_ptr<T> ptr;
        int io_uring_read_fd{-1}, io_uring_write_fd{-1}; // NOT POSIX fds!

        constexpr chunk_ptr_() = default;

        constexpr chunk_ptr_(std::shared_ptr<T> ptr_)
            : ptr(std::move(ptr_))
            , io_uring_read_fd(ptr ? ptr->read_fd().first : -1)
            , io_uring_write_fd(ptr ? ptr->write_fd(0).first : -1)
        {
        }
    };

    pid_t const owning_tid_;
    class storage_pool *storage_pool_{nullptr};
    chunk_ptr_<cnv_chunk> cnv_chunk_;
    std::vector<chunk_ptr_<seq_chunk>> seq_chunks_;

    struct
    {
        int msgread, msgwrite;
    } fds_;

    monad::io::Ring &uring_, *wr_uring_{nullptr};
    monad::io::Buffers &rwbuf_;
    monad::io::BufferPool rd_pool_;
    monad::io::BufferPool wr_pool_;
    bool eager_completions_{false};
    bool capture_io_latencies_{false};

    // IO records
    IORecord records_;
    unsigned concurrent_read_io_limit_{0};

    struct
    {
        unsigned count{0};
        erased_connected_operation *first{nullptr}, *last{nullptr};
    } concurrent_read_ios_pending_;

    void submit_request_(
        std::span<std::byte> buffer, chunk_offset_t chunk_and_offset,
        void *uring_data, enum erased_connected_operation::io_priority prio);
    void submit_request_(
        std::span<const struct iovec> buffers, chunk_offset_t chunk_and_offset,
        void *uring_data, enum erased_connected_operation::io_priority prio);
    void submit_request_(
        std::span<std::byte const> buffer, chunk_offset_t chunk_and_offset,
        void *uring_data, enum erased_connected_operation::io_priority prio);
    void submit_request_(timed_invocation_state *state, void *uring_data);

    void poll_uring_while_submission_queue_full_();
    bool poll_uring_(bool blocking, unsigned poll_rings_mask);

public:
    AsyncIO(class storage_pool &pool, monad::io::Buffers &rwbuf);

    ~AsyncIO();

    pid_t owning_thread_id() const noexcept
    {
        return owning_tid_;
    }

    bool is_read_only() const noexcept
    {
        return rwbuf_.is_read_only();
    }

    class storage_pool &storage_pool() noexcept
    {
        MONAD_DEBUG_ASSERT(storage_pool_ != nullptr);
        return *storage_pool_;
    }

    const class storage_pool &storage_pool() const noexcept
    {
        MONAD_DEBUG_ASSERT(storage_pool_ != nullptr);
        return *storage_pool_;
    }

    size_t chunk_count() const noexcept
    {
        return seq_chunks_.size();
    }

    file_offset_t chunk_capacity(size_t id) const noexcept
    {
        MONAD_ASSERT_PRINTF(
            id < seq_chunks_.size(),
            "id %zu seq chunks size %zu",
            id,
            seq_chunks_.size());
        return seq_chunks_[id].ptr->capacity();
    }

    //! The instance for this thread
    static AsyncIO *thread_instance() noexcept
    {
        return detail::AsyncIO_thread_instance();
    }

    unsigned io_in_flight() const noexcept
    {
        return records_.inflight_rd + concurrent_read_ios_pending_.count +
               records_.inflight_rd_scatter + records_.inflight_wr +
               records_.inflight_tm +
               records_.inflight_ts.load(std::memory_order_relaxed) +
               deferred_initiations_in_flight();
    }

    unsigned reads_in_flight() const noexcept
    {
        return records_.inflight_rd + concurrent_read_ios_pending_.count;
    }

    unsigned max_reads_in_flight() const noexcept
    {
        return records_.max_inflight_rd;
    }

    unsigned reads_scatter_in_flight() const noexcept
    {
        return records_.inflight_rd_scatter;
    }

    unsigned max_reads_scatter_in_flight() const noexcept
    {
        return records_.max_inflight_rd_scatter;
    }

    unsigned writes_in_flight() const noexcept
    {
        return records_.inflight_wr;
    }

    unsigned max_writes_in_flight() const noexcept
    {
        return records_.max_inflight_wr;
    }

    unsigned timers_in_flight() const noexcept
    {
        return records_.inflight_tm;
    }

    unsigned deferred_initiations_in_flight() const noexcept;

    unsigned threadsafeops_in_flight() const noexcept
    {
        return records_.inflight_ts.load(std::memory_order_relaxed);
    }

    unsigned concurrent_read_io_limit() const noexcept
    {
        return concurrent_read_io_limit_;
    }

    void set_concurrent_read_io_limit(unsigned v) noexcept
    {
        concurrent_read_io_limit_ = v;
    }

    bool eager_completions() const noexcept
    {
        return eager_completions_;
    }

    void set_eager_completions(bool v) noexcept
    {
        eager_completions_ = v;
    }

    bool capture_io_latencies() const noexcept
    {
        return capture_io_latencies_;
    }

    void set_capture_io_latencies(bool v) noexcept
    {
        capture_io_latencies_ = v;
    }

    // The number of submission and completion entries remaining right now. Can
    // be stale as soon as it is returned
    std::pair<unsigned, unsigned>
    io_uring_ring_entries_left(bool for_wr_ring) const noexcept;

    // Useful for taking a copy of anonymous inode files used by the unit tests
    void dump_fd_to(size_t which, std::filesystem::path const &path);

    // Blocks until at least one completion is processed, returning number
    // of completions processed.
    size_t poll_blocking(size_t count = 1)
    {
        size_t n = 0;
        for (; n < count; n++) {
            if (!poll_uring_(n == 0, 0)) {
                break;
            }
        }
        return n;
    }

    std::optional<size_t>
    poll_blocking_if_not_within_completions(size_t count = 1)
    {
        if (detail::AsyncIO_per_thread_state().am_within_completions()) {
            return std::nullopt;
        }
        return poll_blocking(count);
    }

    // Never blocks
    size_t poll_nonblocking(size_t count = size_t(-1))
    {
        size_t n = 0;
        for (; n < count; n++) {
            if (!poll_uring_(false, 0)) {
                break;
            }
        }
        return n;
    }

    std::optional<size_t>
    poll_nonblocking_if_not_within_completions(size_t count = size_t(-1))
    {
        if (detail::AsyncIO_per_thread_state().am_within_completions()) {
            return std::nullopt;
        }
        return poll_nonblocking(count);
    }

    void wait_until_done()
    {
        while (io_in_flight() > 0) {
            poll_blocking(size_t(-1));
        }
    }

    void flush()
    {
        wait_until_done();
    }

    void reset_records()
    {
        records_.max_inflight_rd = 0;
        records_.max_inflight_rd_scatter = 0;
        records_.max_inflight_wr = 0;
        records_.nreads = 0;
    }

    size_t submit_read_request(
        std::span<std::byte> buffer, chunk_offset_t offset,
        erased_connected_operation *uring_data)
    {
        if (concurrent_read_io_limit_ > 0) {
            if (records_.inflight_rd >= concurrent_read_io_limit_) {
                auto *state = (erased_connected_operation *)uring_data;
                erased_connected_operation::rbtree_node_traits::set_right(
                    state, nullptr);
                if (concurrent_read_ios_pending_.last == nullptr) {
                    MONAD_DEBUG_ASSERT(
                        concurrent_read_ios_pending_.first == nullptr);
                    concurrent_read_ios_pending_.first =
                        concurrent_read_ios_pending_.last = state;
                    MONAD_DEBUG_ASSERT(concurrent_read_ios_pending_.count == 0);
                }
                else {
                    MONAD_DEBUG_ASSERT(
                        erased_connected_operation::rbtree_node_traits::
                            get_right(concurrent_read_ios_pending_.last) ==
                        nullptr);
                    erased_connected_operation::rbtree_node_traits::set_right(
                        concurrent_read_ios_pending_.last, state);
                    concurrent_read_ios_pending_.last = state;
                }
                concurrent_read_ios_pending_.count++;
                return size_t(-1); // we never complete immediately
            }
        }

        if (capture_io_latencies_) {
            uring_data->initiated = std::chrono::steady_clock::now();
        }
        submit_request_(buffer, offset, uring_data, uring_data->io_priority());
        if (++records_.inflight_rd > records_.max_inflight_rd) {
            records_.max_inflight_rd = records_.inflight_rd;
        }
        ++records_.nreads;
        return size_t(-1); // we never complete immediately
    }

    size_t submit_read_request(
        std::span<const struct iovec> buffers, chunk_offset_t offset,
        erased_connected_operation *uring_data)

    {
        if (capture_io_latencies_) {
            uring_data->initiated = std::chrono::steady_clock::now();
        }
        submit_request_(buffers, offset, uring_data, uring_data->io_priority());
        if (++records_.inflight_rd_scatter > records_.max_inflight_rd_scatter) {
            records_.max_inflight_rd_scatter = records_.inflight_rd_scatter;
        }
        ++records_.nreads;
        return size_t(-1); // we never complete immediately
    }

    void submit_write_request(
        std::span<std::byte const> buffer, chunk_offset_t offset,
        erased_connected_operation *uring_data)
    {
        if (capture_io_latencies_) {
            uring_data->initiated = std::chrono::steady_clock::now();
        }
        submit_request_(buffer, offset, uring_data, uring_data->io_priority());
        if (++records_.inflight_wr > records_.max_inflight_wr) {
            records_.max_inflight_wr = records_.inflight_wr;
        }
    }

    // WARNING: Must exist until completion!
    struct timed_invocation_state
    {
        struct __kernel_timespec ts
        {
            0, 0
        };

        bool timespec_is_absolute{false};
        bool timespec_is_utc_clock{false};
    };

    void submit_timed_invocation_request(
        timed_invocation_state *info, erased_connected_operation *uring_data)
    {
        submit_request_(info, uring_data);
        if (capture_io_latencies_) {
            uring_data->initiated = std::chrono::steady_clock::now();
        }
        ++records_.inflight_tm;
    }

    /* This isn't the ideal place to put this, but only AsyncIO knows how to
    get i/o buffers into which to place connected i/o states.
    */
    static constexpr size_t MAX_CONNECTED_OPERATION_SIZE = DISK_PAGE_SIZE;
    static constexpr size_t READ_BUFFER_SIZE = 8 * DISK_PAGE_SIZE;
    static constexpr size_t WRITE_BUFFER_SIZE = 8 * 1024 * 1024;
    static constexpr size_t MONAD_IO_BUFFERS_READ_SIZE = READ_BUFFER_SIZE;
    static constexpr size_t MONAD_IO_BUFFERS_WRITE_SIZE = WRITE_BUFFER_SIZE;

private:
    struct connected_operation_storage_
    {
        std::byte v[MAX_CONNECTED_OPERATION_SIZE];
    };

    using connected_operation_storage_allocator_type_ =
        allocators::malloc_free_allocator<connected_operation_storage_>;

    connected_operation_storage_allocator_type_
        connected_operation_storage_pool_;

public:
    // Only used with write ops
    template <class ConnectedOperationType>
    struct registered_io_buffer_with_connected_operation
    {
        alignas(DMA_PAGE_SIZE) std::byte write_buffer[WRITE_BUFFER_SIZE];

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
        ConnectedOperationType state[0];
#pragma GCC diagnostic pop

        constexpr registered_io_buffer_with_connected_operation() {}
    };
    friend struct io_connected_operation_unique_ptr_deleter;

    struct io_connected_operation_unique_ptr_deleter
    {
        void operator()(erased_connected_operation *p) const
        {
            auto *io = p->executor();
            p->~erased_connected_operation();
#ifndef NDEBUG
            memset((void *)p, 0xff, MAX_CONNECTED_OPERATION_SIZE);
#endif
            using traits = std::allocator_traits<
                connected_operation_storage_allocator_type_>;
            traits::deallocate(
                io->connected_operation_storage_pool_,
                (connected_operation_storage_ *)p,
                1);
        }
    };

    using erased_connected_operation_unique_ptr_type = std::unique_ptr<
        erased_connected_operation, io_connected_operation_unique_ptr_deleter>;
    template <sender Sender, receiver Receiver>
    using connected_operation_unique_ptr_type = std::unique_ptr<
        decltype(connect(
            std::declval<AsyncIO &>(), std::declval<Sender>(),
            std::declval<Receiver>())),
        io_connected_operation_unique_ptr_deleter>;

    void do_free_read_buffer(std::byte *b) noexcept
    {
#ifndef NDEBUG
        memset((void *)b, 0xff, READ_BUFFER_SIZE);
#endif
        rd_pool_.release((unsigned char *)b);
    }

    void do_free_write_buffer(std::byte *b) noexcept
    {
#ifndef NDEBUG
        static_assert(WRITE_BUFFER_SIZE >= CPU_PAGE_SIZE);
        memset((void *)b, 0xff, CPU_PAGE_SIZE);
#endif
        wr_pool_.release((unsigned char *)b);
    }

    using read_buffer_ptr = detail::read_buffer_ptr;
    using write_buffer_ptr = detail::write_buffer_ptr;

    read_buffer_ptr get_read_buffer(size_t bytes) noexcept
    {
        MONAD_DEBUG_ASSERT(bytes <= READ_BUFFER_SIZE);
        unsigned char *mem = rd_pool_.alloc();
        if (mem == nullptr) {
            mem = poll_uring_while_no_io_buffers_(false);
        }
        return read_buffer_ptr(
            (std::byte *)mem, detail::read_buffer_deleter(this));
    }

    write_buffer_ptr get_write_buffer() noexcept
    {
        unsigned char *mem = wr_pool_.alloc();
        if (mem == nullptr) {
            mem = poll_uring_while_no_io_buffers_(true);
        }
        return write_buffer_ptr(
            (std::byte *)mem, detail::write_buffer_deleter(this));
    }

private:
    unsigned char *poll_uring_while_no_io_buffers_(bool is_write);

    template <bool is_write, class F>
    auto make_connected_impl_(F &&connect)
    {
        using connected_type = decltype(connect());
        static_assert(sizeof(connected_type) <= MAX_CONNECTED_OPERATION_SIZE);
        using traits =
            std::allocator_traits<connected_operation_storage_allocator_type_>;
        unsigned char *mem = (unsigned char *)traits::allocate(
            connected_operation_storage_pool_, 1);
        MONAD_ASSERT_PRINTF(
            mem != nullptr, "failed due to %s", strerror(errno));
        MONAD_DEBUG_ASSERT(((void)mem[0], true));
        auto ret = std::unique_ptr<
            connected_type,
            io_connected_operation_unique_ptr_deleter>(
            new (mem) connected_type(connect()));
        // Did you accidentally pass in a foreign buffer to use?
        // Can't do that, must use buffer returned.
        MONAD_DEBUG_ASSERT(ret->sender().buffer().data() == nullptr);
        if constexpr (is_write) {
            MONAD_DEBUG_ASSERT(rwbuf_.get_write_size() >= WRITE_BUFFER_SIZE);
            auto buffer = std::move(ret->sender()).buffer();
            buffer.set_write_buffer(get_write_buffer());
            ret->sender().reset(ret->sender().offset(), std::move(buffer));
        }
        else {
            MONAD_DEBUG_ASSERT(rwbuf_.get_read_size() >= READ_BUFFER_SIZE);
        }
        return ret;
    }

public:
    //! Construct into internal memory a connected state for an i/o read
    //! or write (not timed delay)
    template <sender Sender, receiver Receiver>
        requires(
            (Sender::my_operation_type == operation_type::read ||
             Sender::my_operation_type == operation_type::write) &&
            requires(
                Receiver r, erased_connected_operation *o,
                typename Sender::result_type x) {
                r.set_value(o, std::move(x));
            })
    auto make_connected(Sender &&sender, Receiver &&receiver)
    {
        return make_connected_impl_<
            Sender::my_operation_type == operation_type::write>([&] {
            return connect<Sender, Receiver>(
                *this, std::move(sender), std::move(receiver));
        });
    }

    //! Construct into internal memory a connected state for an i/o read
    //! or write (not timed delay)
    template <
        sender Sender, receiver Receiver, class... SenderArgs,
        class... ReceiverArgs>
        requires(
            (Sender::my_operation_type == operation_type::read ||
             Sender::my_operation_type == operation_type::write) &&
            requires(
                Receiver r, erased_connected_operation *o,
                typename Sender::result_type x) {
                r.set_value(o, std::move(x));
            } &&
            std::is_constructible_v<Sender, SenderArgs...> &&
            std::is_constructible_v<Receiver, ReceiverArgs...>)
    auto make_connected(
        std::piecewise_construct_t _, std::tuple<SenderArgs...> &&sender_args,
        std::tuple<ReceiverArgs...> &&receiver_args)
    {
        return make_connected_impl_<
            Sender::my_operation_type == operation_type::write>([&] {
            return connect<Sender, Receiver>(
                *this, _, std::move(sender_args), std::move(receiver_args));
        });
    }

    template <class Base, sender Sender, receiver Receiver>
    void notify_operation_initiation_success_(
        detail::connected_operation_storage<Base, Sender, Receiver> *state)
    {
        (void)state;
#if MONAD_TRIE_ENABLE_WRITEBACK_CACHE
        if constexpr (detail::connected_operation_storage<
                          Base,
                          Sender,
                          Receiver>::is_write()) {
            auto *p =
                erased_connected_operation::rbtree_node_traits::to_node_ptr(
                    state);
            erased_connected_operation::rbtree_node_traits::set_key(
                p, state->sender().offset().raw());
            MONAD_DEBUG_ASSERT(p->key == state->sender().offset().raw());
            extant_write_operations_::init(p);
            auto pred = [](auto const *a, auto const *b) {
                auto get_key = [](auto const *a) {
                    return erased_connected_operation::rbtree_node_traits::
                        get_key(a);
                };
                return get_key(a) > get_key(b);
            };
            extant_write_operations_::insert_equal_lower_bound(
                &extant_write_operations_header_, p, pred);
        }
#endif
    }

    template <class Base, sender Sender, receiver Receiver>
    void notify_operation_reset_(
        detail::connected_operation_storage<Base, Sender, Receiver> *state)
    {
        (void)state;
    }

    template <class Base, sender Sender, receiver Receiver, class T>
    void notify_operation_completed_(
        detail::connected_operation_storage<Base, Sender, Receiver> *state,
        result<T> &res)
    {
        (void)state;
        (void)res;
#if MONAD_TRIE_ENABLE_WRITEBACK_CACHE
        if constexpr (detail::connected_operation_storage<
                          Base,
                          Sender,
                          Receiver>::is_write()) {
            extant_write_operations_::erase(
                &extant_write_operations_header_,
                erased_connected_operation::rbtree_node_traits::to_node_ptr(
                    state));
        }
        else if constexpr (
            detail::connected_operation_storage<Base, Sender, Receiver>::
                is_read() &&
            !std::is_void_v<T>) {
            if (res && res.assume_value() > 0) {
                // If we filled the data from extant write buffers above, adjust
                // bytes transferred to account for that.
                res = success(
                    res.assume_value() +
                    erased_connected_operation::rbtree_node_traits::get_key(
                        state));
            }
        }
#endif
    }

private:
    using extant_write_operations_ = ::boost::intrusive::rbtree_algorithms<
        erased_connected_operation::rbtree_node_traits>;
    erased_connected_operation::rbtree_node_traits::node
        extant_write_operations_header_;
};

using erased_connected_operation_ptr =
    AsyncIO::erased_connected_operation_unique_ptr_type;

static_assert(sizeof(AsyncIO) == 224);
static_assert(alignof(AsyncIO) == 8);

namespace detail
{
    inline void read_buffer_deleter::operator()(std::byte *b)
    {
        parent_->do_free_read_buffer(b);
    }

    inline void write_buffer_deleter::operator()(std::byte *b)
    {
        parent_->do_free_write_buffer(b);
    }
}

MONAD_ASYNC_NAMESPACE_END
