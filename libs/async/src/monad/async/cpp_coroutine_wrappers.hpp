#pragma once

#include "io_worker_pool.hpp"

#include "detail/boost_outcome_coroutine_support.hpp"

#include <optional>

#ifndef MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER
//    #include <iostream>
//    #define MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER(...) std::cout << "*** " <<
//    __VA_ARGS__ << std::endl;
    #define MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER(...)
#endif

MONAD_ASYNC_NAMESPACE_BEGIN

//! \brief Concept matching an awaitable
template <class T>
concept awaitable = requires(T x, std::coroutine_handle<> h) {
    {
        x.await_ready()
    } -> std::same_as<bool>;
    x.await_suspend(h);
    x.await_resume();
};

namespace detail
{
    template <sender Sender>
    struct is_io_internal_buffer_sender_type : std::false_type
    {
    };

    template <>
    struct is_io_internal_buffer_sender_type<read_single_buffer_sender>
        : std::true_type
    {
    };

    template <>
    struct is_io_internal_buffer_sender_type<write_single_buffer_sender>
        : std::true_type
    {
    };

    template <
        sender Sender, receiver Receiver,
        bool = is_io_internal_buffer_sender_type<Sender>::value>
    struct connected_stateimpl_
    {
        using connected_state_type = decltype(connect(
            std::declval<AsyncIO &>(), std::declval<Sender>(),
            std::declval<Receiver>()));

        static connected_state_type make(AsyncIO &io, Sender &&sender)
        {
            return connect(io, std::move(sender), Receiver{});
        }

        template <class... SenderArgs>
        static connected_state_type make(
            AsyncIO &io, std::piecewise_construct_t _,
            std::tuple<SenderArgs...> &&sender_args)
        {
            return connect<Sender, Receiver>(
                io, _, std::move(sender_args), std::tuple{});
        }

        static connected_state_type &access(connected_state_type &v)
        {
            return v;
        }

        static connected_state_type const &access(connected_state_type const &v)
        {
            return v;
        }
    };

    template <sender Sender, receiver Receiver>
    struct connected_stateimpl_<Sender, Receiver, true>
    {
        using connected_state_type =
            AsyncIO::connected_operation_unique_ptr_type<Sender, Receiver>;

        static connected_state_type make(AsyncIO &io, Sender &&sender)
        {
            return io.make_connected(std::move(sender), Receiver{});
        }

        template <class... SenderArgs>
        static connected_state_type make(
            AsyncIO &io, std::piecewise_construct_t _,
            std::tuple<SenderArgs...> &&sender_args)
        {
            return io.make_connected<Sender, Receiver>(
                _, std::move(sender_args), std::tuple{});
        }

        static connected_state_type::element_type &
        access(connected_state_type &v)
        {
            return *v;
        }

        static connected_state_type::element_type const &
        access(connected_state_type const &v)
        {
            return *v;
        }
    };

    template <sender Sender>
    class awaitable
    {
        using result_type_ = typename Sender::result_type;

        class receiver_t_
        {
            friend class awaitable;
            std::optional<result_type_> result_;
            std::coroutine_handle<> cont_;

        public:
            // We need AsyncIO to not recycle the i/o state until the future
            // gets destructed, so take over lifetime management outselves
            enum : bool
            {
                lifetime_managed_internally = false
            };

            // The receiver machinery
            void set_value(erased_connected_operation *, result_type_ res)
            {
                MONAD_DEBUG_ASSERT(!result_.has_value());
                result_.emplace(std::move(res));
                if (cont_) {
                    MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER(
                        this << " receiver resumes coroutine "
                             << cont_.address());
                    cont_.resume();
                }
            }

            void reset()
            {
                result_ = {};
                cont_ = {};
            }
        };

        using impl_ = detail::connected_stateimpl_<Sender, receiver_t_>;
        using connected_state_type_ = typename impl_::connected_state_type;

        connected_state_type_ state_;

    public:
        template <class... Args>
        awaitable(Args &&...args)
            : state_(impl_::make(std::forward<Args>(args)...))
        {
            MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER(
                &impl_::access(state_).receiver() << " initiates operation");
            impl_::access(state_).initiate();
        }

        bool await_ready() const noexcept
        {
            MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER(
                &impl_::access(state_).receiver()
                << " await_ready = "
                << impl_::access(state_).receiver().result_.has_value());
            return impl_::access(state_).receiver().result_.has_value();
        }

        void await_suspend(std::coroutine_handle<> cont)
        {
            MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER(
                &impl_::access(state_).receiver()
                << " await_suspend coroutine " << cont.address());
            MONAD_DEBUG_ASSERT(impl_::access(state_).receiver().cont_ == nullptr);
            impl_::access(state_).receiver().cont_ = cont;
        }

        result_type_ await_resume()
        {
            MONAD_ASYNC_AWAITABLES_DEBUG_PRINTER(
                &impl_::access(state_).receiver() << " await_resume");
            MONAD_DEBUG_ASSERT(await_ready());
            return std::move(*impl_::access(state_).receiver().result_);
        }
    };
}

//! \brief Initiate the execution of a Sender on a specific `AsyncIO`
//! instance, returning an awaitable which can be `co_await`ed upon.
template <sender Sender>
[[nodiscard]] auto co_initiate(AsyncIO &io, Sender &&sender)
{
    return detail::awaitable<Sender>{io, std::move(sender)};
}

//! \brief Initiate the execution of a Sender on a specific `AsyncIO`
//! instance, returning an awaitable which can be `co_await`ed upon.
template <sender Sender, class... SenderArgs>
    requires(std::is_constructible_v<Sender, SenderArgs...>)
[[nodiscard]] auto co_initiate(
    AsyncIO &io, std::piecewise_construct_t _,
    std::tuple<SenderArgs...> &&sender_args)
{
    return detail::awaitable<Sender>{
        io, _, std::forward<SenderArgs>(sender_args)...};
}

//! \brief Convenience wrapper initiating a callable returning an awaitable
//! on a `` instance, returning an awaitable which readies when the callable
//! readies its awaitable on the worker thread.
template <class... QueueOptions, class F>
    requires(awaitable<std::invoke_result_t<F, erased_connected_operation *>>)
[[nodiscard]] auto
co_initiate(AsyncIO &io, AsyncReadIoWorkerPool<QueueOptions...> &pool, F f)
{
    using co_return_type =
        decltype(f(std::declval<erased_connected_operation *>())
                     .await_resume());

    struct invoke_coroutine_sender
    {
        using result_type = co_return_type;

        F f;
        std::optional<awaitables::eager<void>> aw;
        std::optional<co_return_type> res;

        invoke_coroutine_sender(F &&_f)
            : f(std::move(_f))
        {
        }

        result<void> operator()(erased_connected_operation *io_state) noexcept
        {
            aw.emplace(co_initiate(io_state));
            return success();
        }

        awaitables::eager<void>
        co_initiate(erased_connected_operation *io_state)
        {
            res = co_await f(io_state);
            io_state->completed(success());
            co_return;
        }

        result_type
        completed(erased_connected_operation *, result<void>) noexcept
        {
            return std::move(res).value();
        }
    };

    return detail::awaitable<execute_on_worker_pool<invoke_coroutine_sender>>{
        io,
        execute_on_worker_pool<invoke_coroutine_sender>(pool, std::move(f))};
}

//! \brief Suspend execution on the current `AsyncIO`, and resume execution on
//! the specified `AsyncIO`
[[nodiscard]] inline auto co_resume_execution_upon(AsyncIO &io)
{
    class awaitable
    {
        class receiver_t_
        {
            friend class awaitable;
            std::atomic<bool> ready_{false};
            std::optional<result<void>> result_;
            std::coroutine_handle<> cont_;

        public:
            // We need AsyncIO to not recycle the i/o state until the future
            // gets destructed, so take over lifetime management outselves
            enum : bool
            {
                lifetime_managed_internally = false
            };

            // The receiver machinery
            void set_value(erased_connected_operation *, result<void> res)
            {
                MONAD_DEBUG_ASSERT(!result_.has_value());
                result_.emplace(std::move(res));
                ready_.store(true, std::memory_order_release);
                if (cont_) {
                    cont_.resume();
                }
            }

            void reset()
            {
                result_ = {};
                cont_ = {};
            }
        };

        using impl_ =
            detail::connected_stateimpl_<threadsafe_sender, receiver_t_>;
        using connected_state_type_ = typename impl_::connected_state_type;

        connected_state_type_ state_;

    public:
        awaitable(AsyncIO &io)
            : state_(impl_::make(io, std::piecewise_construct, std::tuple{}))
        {
        }

        bool await_ready() const noexcept
        {
            return impl_::access(state_).receiver().ready_.load(
                std::memory_order_acquire);
        }

        void await_suspend(std::coroutine_handle<> cont)
        {
            MONAD_DEBUG_ASSERT(impl_::access(state_).receiver().cont_ == nullptr);
            impl_::access(state_).receiver().cont_ = cont;
            impl_::access(state_).initiate();
        }

        result<void> await_resume()
        {
            MONAD_DEBUG_ASSERT(await_ready());
            return std::move(*impl_::access(state_).receiver().result_);
        }
    };

    return awaitable{io};
}

MONAD_ASYNC_NAMESPACE_END
