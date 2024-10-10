#pragma once

#include "io_senders.hpp"

#include <atomic>
#include <mutex>
#include <optional>
#include <semaphore>
#include <thread>
#include <vector>

#include <fcntl.h>

#include <boost/lockfree/queue.hpp>

#include <monad/core/tl_tid.h>

MONAD_ASYNC_NAMESPACE_BEGIN

template <sender Sender>
class execute_on_worker_pool;

namespace detail
{
    template <class...>
    struct EmptyTypeList
    {
    };

    struct AsyncReadIoWorkerPoolBase
    {
        template <sender Sender>
        friend class MONAD_ASYNC_NAMESPACE::execute_on_worker_pool;

        virtual ~AsyncReadIoWorkerPoolBase() {}

        //! Threadsafe. Returns the master `AsyncIO` instance for this worker
        //! pool.
        AsyncIO &master_controller() noexcept
        {
            return parent_io_;
        }

        struct customisation_points
        {
            virtual ~customisation_points() {}

            //! If the worker thread is idle, this customisation point lets
            //! subclasses begin other new work. If sleeping the worker thread
            //! is desired, return false. Return true to keep the worker thread
            //! spin looping.
            virtual bool try_initiate_other_work(bool io_is_pending) = 0;
        };

        //! If the worker thread is idle, this customisation point lets
        //! subclasses begin other new work. If sleeping the worker thread
        //! is desired, return false. Return true to keep the worker thread
        //! spin looping.
        bool try_initiate_other_work(bool io_is_pending)
        {
            if (customisation_points_) {
                return customisation_points_->try_initiate_other_work(
                    io_is_pending);
            }
            return false;
        }

        virtual bool try_submit_work_item(erased_connected_operation *item) = 0;

    protected:
        AsyncReadIoWorkerPoolBase(
            AsyncIO &parent_io,
            std::unique_ptr<customisation_points> customisation_points_)
            : parent_io_(parent_io)
            , customisation_points_(std::move(customisation_points_))
        {
        }

    private:
        AsyncIO &parent_io_;
        std::unique_ptr<customisation_points> customisation_points_;
    };

    template <class T, class QueueOptions>
    struct BoostLockfreeQueueFactory;

    template <
        class T, template <class...> class TypeList, class... QueueOptions>
    struct BoostLockfreeQueueFactory<T, TypeList<QueueOptions...>>
    {
        using type = ::boost::lockfree::queue<T, QueueOptions...>;
        static constexpr bool has_capacity =
            ::boost::lockfree::detail::extract_capacity<
                typename ::boost::lockfree::detail::queue_signature::bind<
                    QueueOptions...>::type>::has_capacity;
    };

    template <class QueueOptions>
    class AsyncReadIoWorkerPoolImpl : public AsyncReadIoWorkerPoolBase
    {
        enum class thread_status
        {
            sleeping,
            idle_io_pending,
            working
        };

        struct worker_t_
        {
            struct thread_state_t
            {
                AsyncReadIoWorkerPoolImpl &parent_pool;
                monad::io::Ring ring;
                monad::io::Buffers buf;
                AsyncIO local_io;
                std::atomic<thread_status> status{thread_status::working};

                template <class U, class V>
                thread_state_t(
                    AsyncReadIoWorkerPoolImpl &parent_pool_, U &&make_ring,
                    V &&make_buffers)
                    : parent_pool(parent_pool_)
                    , ring(make_ring())
                    , buf(make_buffers(ring))
                    , local_io(
                          parent_pool.master_controller().storage_pool(), buf)
                {
                }

                void iterate()
                {
                    // If there are i/o completions ready, process those first
                    status.store(
                        thread_status::working, std::memory_order_release);
                    if (0 == local_io.poll_nonblocking(1)) {
                        bool const io_is_pending =
                                       (local_io.io_in_flight() > 0),
                                   do_not_sleep =
                                       parent_pool.try_initiate_other_work(
                                           io_is_pending);
                        bool pls_take_item = false;
                        if (!io_is_pending && !do_not_sleep) {
                            status.store(
                                thread_status::sleeping,
                                std::memory_order_release);
                            parent_pool.enqueued_workitems_count_.acquire();
                            pls_take_item = true;
                        }
                        else {
                            status.store(
                                thread_status::idle_io_pending,
                                std::memory_order_release);
                            pls_take_item =
                                parent_pool.enqueued_workitems_count_
                                    .try_acquire();
                        }
                        if (pls_take_item) {
                            erased_connected_operation *workitem = nullptr;
                            if (parent_pool.enqueued_workitems_.pop(workitem)) {
                                status.store(
                                    thread_status::working,
                                    std::memory_order_release);
                                std::atomic_thread_fence(
                                    std::memory_order_acquire);
                                workitem->io_.store(
                                    &local_io, std::memory_order_release);
                                workitem->initiate();
                            }
                        }
                        else {
                            // No point wasting a time slice, give it up
                            std::this_thread::yield();
                        }
                    }
                }
            };

            std::atomic<thread_state_t *> thread_state{nullptr};
            std::jthread thread;

            template <class U, class V>
            worker_t_(
                AsyncReadIoWorkerPoolImpl &parent_pool, U &&make_ring,
                V &&make_buffers)
                : thread([&](std::stop_token token) {
                    pthread_setname_np(pthread_self(), "pool worker");
                    auto *ts = new thread_state_t(
                        parent_pool,
                        std::forward<U>(make_ring),
                        std::forward<V>(make_buffers));
                    thread_state.store(ts, std::memory_order_release);
                    while (!token.stop_requested()) {
                        ts->iterate();
                    }
                    ts->local_io.wait_until_done();
                    delete ts;
                    thread_state.store(nullptr, std::memory_order_release);
                })
            {
            }

            worker_t_(worker_t_ const &) = delete;

            worker_t_(worker_t_ &&o) noexcept
                : thread_state(o.thread_state.exchange(
                      nullptr, std::memory_order_acq_rel))
                , thread(std::move(o.thread))
            {
            }

            worker_t_ &operator=(worker_t_ const &) = delete;

            worker_t_ &operator=(worker_t_ &&o) noexcept
            {
                if (this != &o) {
                    this->~worker_t_();
                    new (this) worker_t_(std::move(o));
                }
                return *this;
            }

            ~worker_t_()
            {
                delete thread_state.load(std::memory_order_acquire);
            }
        };
        friend struct worker_t_::thread_state_t;
        using boost_lockfree_queue_type_ = typename BoostLockfreeQueueFactory<
            erased_connected_operation *, QueueOptions>::type;

        // Safe to access without locking
        std::binary_semaphore enqueued_workitems_count_{0};
        boost_lockfree_queue_type_ enqueued_workitems_{[] {
            if constexpr (BoostLockfreeQueueFactory<
                              erased_connected_operation *,
                              QueueOptions>::has_capacity) {
                return boost_lockfree_queue_type_{}; // default constructor to
                                                     // be used for fixed
                                                     // capacity queues
            }
            else {
                return boost_lockfree_queue_type_{16}; // initial free list
            }
        }()};

        // Unsafe to modify without locking
        std::vector<worker_t_> workers_;

    protected:
        template <class U, class V>
        void initialise_(size_t workers, U &&make_ring, V &&make_buffers)
        {
            workers_.reserve(workers);
            for (size_t n = 0; n < workers; n++) {
                workers_.emplace_back(
                    *this,
                    std::forward<U>(make_ring),
                    std::forward<V>(make_buffers));
            }
            while (!currently_idle()) {
                std::this_thread::yield();
            }
        }

    public:
        explicit AsyncReadIoWorkerPoolImpl(
            AsyncIO &parent,
            std::unique_ptr<
                detail::AsyncReadIoWorkerPoolBase::customisation_points>
                customisation_points)
            : detail::AsyncReadIoWorkerPoolBase(
                  parent, std::move(customisation_points))
        {
        }

        ~AsyncReadIoWorkerPoolImpl()
        {
            MONAD_ASSERT(no_items_waiting());
            for (auto &i : workers_) {
                i.thread.request_stop();
            }
            enqueued_workitems_count_.release(
                static_cast<ptrdiff_t>(workers_.size()));
            for (auto &i : workers_) {
                i.thread.join();
            }
            std::atomic_thread_fence(std::memory_order_acq_rel);
            workers_.clear();
        }

        //! Threadsafe. Returns the number of thread workers this pool has.
        [[nodiscard]] size_t workers() const noexcept
        {
            return workers_.size();
        }

        //! Threadsafe. True if all submitted items are being worked upon, which
        //! includes no items
        [[nodiscard]] bool no_items_waiting() const noexcept
        {
            return enqueued_workitems_.empty();
        }

        //! Threadsafe but can be false positive and false negative. True if the
        //! worker pool is currently idle and has no work
        [[nodiscard]] bool currently_idle() const noexcept
        {
            for (auto &i : workers_) {
                if (auto *ts = i.thread_state.load(std::memory_order_acquire);
                    ts != nullptr &&
                    ts->status.load(std::memory_order_acquire) !=
                        thread_status::sleeping) {
                    return false;
                }
            }
            return no_items_waiting();
        }

        //! Threadsafe but unstable. Return an estimate of how busy the workers
        //! are, with `1.0` = completely busy.
        [[nodiscard]] float busy_estimate() const noexcept
        {
            int ret = 0;
            for (auto &i : workers_) {
                if (auto *ts = i.thread_state.load(std::memory_order_acquire);
                    ts != nullptr) {
                    switch (ts->status.load(std::memory_order_acquire)) {
                    case thread_status::sleeping:
                        break;
                    case thread_status::idle_io_pending:
                        ret += 1;
                        break;
                    case thread_status::working:
                        ret += 2;
                        break;
                    }
                }
            }
            return float(ret) / static_cast<float>(workers_.size() * 2);
        }

        virtual bool
        try_submit_work_item(erased_connected_operation *item) override final
        {
            // All writes to global state must be flushed before other threads
            // may acquire reads
            std::atomic_thread_fence(std::memory_order_release);
            auto ret = enqueued_workitems_.push(item);
            if (ret) {
                enqueued_workitems_count_.release();
            }
            return ret;
        }
    };
}

/*! \class AsyncReadIoWorkerPool
\brief Lets you outsource compute and read i/o to worker threads.
\tparam QueueOptions Any options which `boost::lockfree::queue` can take.
The most common is to make the work queue fixed capacity to avoid all
dynamic memory allocations.

NOTE: These workers are incapable of writing to the file, they can only
read. Only the parent `AsyncIO` can write to the file. Therefore there
is no point supplying write buffers for workers to use.
*/
template <class QueueOptions = detail::EmptyTypeList<>>
class AsyncReadIoWorkerPool final
    : public detail::AsyncReadIoWorkerPoolImpl<QueueOptions>
{
    using base_ = detail::AsyncReadIoWorkerPoolImpl<QueueOptions>;

public:
    template <class U, class V>
    AsyncReadIoWorkerPool(
        AsyncIO &parent, size_t workers, U &&make_ring, V &&make_buffers)
        : base_(parent, {})
    {
        base_::initialise_(
            workers, std::forward<U>(make_ring), std::forward<V>(make_buffers));
    }
};

/*! \class execute_on_worker_pool
\brief Wraps a Sender to be initiated at first opportunity by a kernel thread
worker in an `AsyncReadIoWorkerPool` attached to a master `AsyncIO` instance.

Exposes the Sender as a public inheritance, so all its member functions and
typedefs pass through.

After initiation, your Sender must NOT access state outside itself without
appropriate thread synchronisation. For maximum performance, you should try
to copy any state the Sender will need to use during execution into the Sender
before initiation (its constructor is the obvious means here). As with all
Sender initiation, there are three means of exiting initiation:

1. Return `success()`, which means you have set up something else to call
`completed()` on your connected i/o state later from the same kernel thread e.g.
an i/o, a timer, some other Receiver.

2. Return a failure, which means initiation failed and the Receiver is to be
immediately informed of the cause of failure.

3. Return `sender_errc::initiation_immediately_completed` optionally supplying
a custom `bytes_transferred` via `make_status_code()`, this causes the Receiver
to be immediately informed of success.

(None of the above are any different for these wrapped Senders than to any other
Sender)

Upon completion, the Receiver is NOT invoked in the worker thread, it is instead
invoked in the master `AsyncIO` instance. You are therefore free to access
state associated with the master `AsyncIO` instance within the Receiver without
any thread synchronisation.
*/
template <sender Sender>
class execute_on_worker_pool : public Sender
{
public:
    using result_type = typename Sender::result_type;

private:
    static constexpr bool
        base_sender_completed_takes_result_bytes_transferred_ = requires(
            Sender x, erased_connected_operation *y, result<size_t> z) {
            x.completed(y, std::move(z));
        };
    using completed_input_result_type_ = std::conditional_t<
        base_sender_completed_takes_result_bytes_transferred_, result<size_t>,
        result<void>>;

    enum class state_t_
    {
        uninitiated,
        submitted,
        initiated,
        completed_pre_defer,
        completed_post_defer
    };

    struct invoke_receiver_receiver_
    {
        execute_on_worker_pool *parent;
        erased_connected_operation *original_io_state;
        completed_input_result_type_ original_input_result;

        invoke_receiver_receiver_(
            execute_on_worker_pool *parent_,
            erased_connected_operation *original_io_state_,
            completed_input_result_type_ original_input_result_)
            : parent(parent_)
            , original_io_state(original_io_state_)
            , original_input_result(std::move(original_input_result_))
        {
        }

        void set_value(erased_connected_operation *, result<void> res)
        {
            MONAD_ASSERT(res);
            // We are back onto the master AsyncIO instance, issue the
            // completion
            original_io_state->completed(std::move(original_input_result));
        }

        void reset() {}
    };
    friend struct invoke_receiver_receiver_;
    using defer_back_to_master_connected_state_type_ =
        connected_operation<timed_delay_sender, invoke_receiver_receiver_>;
    using reschedule_back_to_master_connected_state_type_ =
        connected_operation<threadsafe_sender, invoke_receiver_receiver_>;

    detail::AsyncReadIoWorkerPoolBase *const pool_{nullptr};
    pid_t const initiating_tid_{0};
    std::atomic<state_t_> state_{state_t_::uninitiated};

    // Stop the connected state making this type immovable
    union reschedule_back_to_master_op_t_
    {
        static constexpr size_t storage_bytes =
            (sizeof(defer_back_to_master_connected_state_type_) <
             sizeof(reschedule_back_to_master_connected_state_type_))
                ? sizeof(reschedule_back_to_master_connected_state_type_)
                : sizeof(defer_back_to_master_connected_state_type_);
        std::byte storage[storage_bytes];
        defer_back_to_master_connected_state_type_ defer_state;
        reschedule_back_to_master_connected_state_type_ reschedule_state;

        reschedule_back_to_master_op_t_() {}

        ~reschedule_back_to_master_op_t_() {}

        void destroy_defer_state()
        {
            defer_state.~defer_back_to_master_connected_state_type_();
        }

        void destroy_reschedule_state()
        {
            reschedule_state.~reschedule_back_to_master_connected_state_type_();
        }
    } reschedule_back_to_master_op_;

    using initiation_result_type_ = decltype(std::declval<Sender>()(
        std::declval<erased_connected_operation *>()));

public:
    execute_on_worker_pool() = default;

    template <class... Args>
        requires(std::is_constructible_v<Sender, Args...>)
    execute_on_worker_pool(
        detail::AsyncReadIoWorkerPoolBase &pool, Args &&...args)
        : Sender(std::forward<Args>(args)...)
        , pool_(&pool)
        , initiating_tid_(get_tl_tid())
    {
    }

    execute_on_worker_pool(execute_on_worker_pool const &) = delete;

    execute_on_worker_pool(execute_on_worker_pool &&o) noexcept
        : Sender(std::move(o))
        , pool_(o.pool_)
        , initiating_tid_(o.initiating_tid_)
        , state_(state_t_::uninitiated)
    {
        MONAD_ASSERT(
            o.state_.load(std::memory_order_acquire) == state_t_::uninitiated);
    }

    execute_on_worker_pool &operator=(execute_on_worker_pool const &) = delete;

    execute_on_worker_pool &operator=(execute_on_worker_pool &&o) noexcept
    {
        if (this != &o) {
            this->~execute_on_worker_pool();
            new (this) execute_on_worker_pool(std::move(o));
        }
        return *this;
    }

    ~execute_on_worker_pool()
    {
        switch (state_.load(std::memory_order_acquire)) {
        case state_t_::completed_pre_defer:
            reschedule_back_to_master_op_.destroy_defer_state();
            break;
        case state_t_::completed_post_defer:
            reschedule_back_to_master_op_.destroy_reschedule_state();
            break;
        default:
            break;
        }
    }

    /*! \brief Initiates the initiation of the wrapped Sender on the next
    available worker thread.

    We do not wait for the remote worker, so the failures returned here are for
    the initiation of the remote execution, not the initiation of the wrapped
    Sender.

    If you configured the pool to have a fixed capacity, if the queue is full
    then a failure comparing equal to `errc::resource_unavailable_try_again`
    will be returned, which shall be passed onto your connected Receiver. It is
    on your Receiver to detect this temporary failure, reset the connected i/o
    state, and reschedule itself to be initiated later (a `timed_delay_sender`
    is suggested).

    If you configured the pool to have dynamic capacity, a failure comparing
    equal to `errc::not_enough_memory` is possible. Your Receiver will be told
    of this.
    */
    initiation_result_type_
    operator()(erased_connected_operation *io_state) noexcept
    {
        MONAD_ASSERT(pool_ != nullptr);
        // We need to do an acquire-release to synchronise the whole of the
        // Sender's state across threads
        switch (state_.load(std::memory_order_acquire)) {
        case state_t_::uninitiated:
            state_.store(state_t_::submitted, std::memory_order_release);
            if (!pool_->try_submit_work_item(io_state)) {
                state_.store(state_t_::uninitiated, std::memory_order_release);
                return errc::resource_unavailable_try_again;
            }
            return success();
        case state_t_::submitted:
            // We are being initiated from within the worker thread
            state_.store(state_t_::initiated, std::memory_order_release);
            return Sender::operator()(io_state);
        case state_t_::initiated:
            // The sender returned operation_must_be_reinitiated
            return Sender::operator()(io_state);
        case state_t_::completed_pre_defer:
            // Our completed() override has returned
            // sender_errc::operation_must_be_reinitiated, so initiate
            // our deferment onto the current kernel thread
            reschedule_back_to_master_op_.defer_state.initiate();
            return success();
        case state_t_::completed_post_defer:
            // Our completed() override has returned
            // sender_errc::operation_must_be_reinitiated, so initiate
            // our rescheduling onto the parent AsyncIO instance
            reschedule_back_to_master_op_.reschedule_state.initiate();
            return success();
        default:
            abort(); // should never happen
        }
        return success();
    }

    result_type completed(
        erased_connected_operation *io_state,
        completed_input_result_type_ res) noexcept
    {
        switch (state_.load(std::memory_order_acquire)) {
        case state_t_::initiated:
            if (initiating_tid_ ==
                    pool_->master_controller().owning_thread_id() &&
                (res || res.assume_error() !=
                            sender_errc::operation_must_be_reinitiated)) {
                // Have me called back after what completes has exited
                new (&reschedule_back_to_master_op_.defer_state)
                    defer_back_to_master_connected_state_type_(connect(
                        *AsyncIO::thread_instance(),
                        timed_delay_sender{std::chrono::seconds(0) /* noop */},
                        invoke_receiver_receiver_(
                            this, io_state, std::move(res))));
                state_.store(
                    state_t_::completed_pre_defer, std::memory_order_release);
                // This will invoke operator() again
                return sender_errc::operation_must_be_reinitiated;
            }
            [[fallthrough]];
        case state_t_::completed_pre_defer:
            if (initiating_tid_ ==
                    pool_->master_controller().owning_thread_id() &&
                (res || res.assume_error() !=
                            sender_errc::operation_must_be_reinitiated)) {
                // Resume execution on the master controller
                reschedule_back_to_master_op_.destroy_defer_state();
                new (&reschedule_back_to_master_op_.reschedule_state)
                    reschedule_back_to_master_connected_state_type_(connect(
                        pool_->master_controller(),
                        threadsafe_sender{},
                        invoke_receiver_receiver_(
                            this, io_state, std::move(res))));
                state_.store(
                    state_t_::completed_post_defer, std::memory_order_release);
                // This will invoke operator() again
                return sender_errc::operation_must_be_reinitiated;
            }
            [[fallthrough]];
        default:
            // In this situation, don't send back to master controller
            if constexpr (requires(Sender x) {
                              x.completed(io_state, std::move(res));
                          }) {
                return Sender::completed(io_state, std::move(res));
            }
            else {
                return res;
            }
        }
    }
};

static_assert(
    sizeof(execute_on_worker_pool<read_single_buffer_sender>) -
        sizeof(read_single_buffer_sender) ==
    152);
static_assert(alignof(execute_on_worker_pool<read_single_buffer_sender>) == 8);
static_assert(sender<execute_on_worker_pool<read_single_buffer_sender>>);

MONAD_ASYNC_NAMESPACE_END
