#pragma once

/* This is locally ported copy of Boost.Outcome's fixed coroutine support
header, until Boost 1.84 it was broken.
*/

#ifndef BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER
//    #include <iostream>
//    #define BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(...)
//        std::cout << __VA_ARGS__ << std::endl;
    #define BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(...)
#endif

#include <boost/outcome/coroutine_support.hpp>

#if BOOST_OUTCOME_VERSION_MAJOR == 2 && BOOST_OUTCOME_VERSION_MINOR == 2 &&    \
    BOOST_OUTCOME_VERSION_PATCH < 8

namespace awaitables
{
    template <class Promise = void>
    using coroutine_handle = std::coroutine_handle<Promise>;
    using std::noop_coroutine;
    namespace detail
    {
        struct error_type_not_found
        {
        };
        struct exception_type_not_found
        {
        };
        template <class T>
        struct type_found
        {
            using type = T;
        };
        template <class T, class U = typename T::error_type>
        constexpr inline type_found<U> extract_error_type(int /*unused*/)
        {
            return {};
        }
        template <class T>
        constexpr inline type_found<error_type_not_found>
        extract_error_type(...)
        {
            return {};
        }
        template <class T, class U = typename T::exception_type>
        constexpr inline type_found<U> extract_exception_type(int /*unused*/)
        {
            return {};
        }
        template <class T>
        constexpr inline type_found<exception_type_not_found>
        extract_exception_type(...)
        {
            return {};
        }

        BOOST_OUTCOME_TEMPLATE(class T, class U)
        BOOST_OUTCOME_TREQUIRES(BOOST_OUTCOME_TPRED(
            BOOST_OUTCOME_V2_NAMESPACE::detail::is_constructible<U, T>))
        inline bool try_set_error(T &&e, U *result)
        {
            new (result) U(static_cast<T &&>(e));
            return true;
        }
        template <class T>
        inline bool try_set_error(T && /*unused*/, ...)
        {
            return false;
        }
        BOOST_OUTCOME_TEMPLATE(class T, class U)
        BOOST_OUTCOME_TREQUIRES(BOOST_OUTCOME_TPRED(
            BOOST_OUTCOME_V2_NAMESPACE::detail::is_constructible<U, T>))
        inline void set_or_rethrow(T &e, U *result)
        {
            new (result) U(e);
        }
        template <class T>
        inline void set_or_rethrow(T &e, ...)
        {
            rethrow_exception(e);
        }
        template <class T>
        class fake_atomic
        {
            T _v;

        public:
            constexpr fake_atomic(T v)
                : _v(v)
            {
            }
            T load(std::memory_order /*unused*/)
            {
                return _v;
            }
            void store(T v, std::memory_order /*unused*/)
            {
                _v = v;
            }
            bool compare_exchange_strong(
                T &expected, T v, std::memory_order /*unused*/,
                std::memory_order /*unused*/)
            {
                if (_v == expected) {
                    _v = v;
                    return true;
                }
                return false;
            }
        };

        template <
            class Awaitable, bool suspend_initial, bool use_atomic,
            bool is_void>
        struct outcome_promise_type
        {
            using container_type = typename Awaitable::container_type;
            using result_set_type = std::conditional_t<
                use_atomic, std::atomic<bool>, fake_atomic<bool>>;
            union
            {
                BOOST_OUTCOME_V2_NAMESPACE::detail::empty_type default_{};
                container_type result;
            };
            result_set_type result_set{false},
                pending_first_resumption{is_initially_suspended};
            coroutine_handle<> continuation;

            static constexpr bool is_initially_suspended = suspend_initial;
            static constexpr bool is_using_atomics = use_atomic;

            outcome_promise_type() noexcept
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise constructed");
            }
            outcome_promise_type(const outcome_promise_type &) = delete;
            outcome_promise_type(outcome_promise_type &&) = delete;
            outcome_promise_type &
            operator=(const outcome_promise_type &) = delete;
            outcome_promise_type &operator=(outcome_promise_type &&) = delete;
            ~outcome_promise_type()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise destructs");
                if (result_set.load(std::memory_order_acquire)) {
                    result.~container_type(); // could throw
                }
            }
            auto get_return_object()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise returns awaitable");
                return Awaitable{*this}; // could throw bad_alloc
            }
            void return_value(container_type &&value)
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise returns value");
                MONAD_DEBUG_ASSERT(!result_set.load(std::memory_order_acquire));
                if (result_set.load(std::memory_order_acquire)) {
                    result.~container_type(); // could throw
                }
                new (&result) container_type(
                    static_cast<container_type &&>(value)); // could throw
                result_set.store(true, std::memory_order_release);
            }
            void return_value(const container_type &value)
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise returns value");
                MONAD_DEBUG_ASSERT(!result_set.load(std::memory_order_acquire));
                if (result_set.load(std::memory_order_acquire)) {
                    result.~container_type(); // could throw
                }
                new (&result) container_type(value); // could throw
                result_set.store(true, std::memory_order_release);
            }
            void unhandled_exception()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise unhandled exception");
                MONAD_DEBUG_ASSERT(!result_set.load(std::memory_order_acquire));
                if (result_set.load(std::memory_order_acquire)) {
                    result.~container_type();
                }
    #ifdef __cpp_exceptions
                auto e = std::current_exception();
                auto ec = BOOST_OUTCOME_V2_NAMESPACE::awaitables::detail::
                    error_from_exception(static_cast<decltype(e) &&>(e), {});
                // Try to set error code first
                if (!BOOST_OUTCOME_V2_NAMESPACE::awaitables::detail::
                        error_is_set(ec) ||
                    !BOOST_OUTCOME_V2_NAMESPACE::awaitables::detail::
                        try_set_error(
                            static_cast<decltype(ec) &&>(ec), &result)) {
                    BOOST_OUTCOME_V2_NAMESPACE::awaitables::detail::
                        set_or_rethrow(e, &result); // could throw
                }
    #else
                std::terminate();
    #endif
                result_set.store(true, std::memory_order_release);
            }
            auto initial_suspend() noexcept
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise initial suspend = " << suspend_initial);
                struct awaiter
                {
                    constexpr bool await_ready() noexcept
                    {
                        return !suspend_initial;
                    }
                    void await_resume() noexcept {}
                    void await_suspend(coroutine_handle<> /*unused*/) noexcept
                    {
                    }
                };
                return awaiter{};
            }
            auto final_suspend() noexcept
            {
                struct awaiter
                {
                    // If we don't force a final suspend, promise will get
                    // deleted before awaitable
                    // TODO: Implement detachable awaitables
                    constexpr bool await_ready() noexcept
                    {
                        return false;
                    }
                    void await_resume() noexcept {}
    #if BOOST_OUTCOME_HAVE_NOOP_COROUTINE
                    coroutine_handle<> await_suspend(
                        coroutine_handle<outcome_promise_type> self) noexcept
                    {
                        if (self.promise().continuation) {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will resume "
                                   "coroutine "
                                << self.promise().continuation.address());
                        }
                        else {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will exit");
                        }
                        return self.promise().continuation
                                   ? self.promise().continuation
                                   : noop_coroutine();
                    }
    #else
                    void
                    await_suspend(coroutine_handle<outcome_promise_type> self)
                    {
                        if (self.promise().continuation) {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will resume "
                                   "coroutine "
                                << self.promise().continuation.address());
                            return self.promise().continuation.resume();
                        }
                        else {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will exit");
                        }
                    }
    #endif
                };
                return awaiter{};
            }
        };
        template <class Awaitable, bool suspend_initial, bool use_atomic>
        struct outcome_promise_type<
            Awaitable, suspend_initial, use_atomic, true>
        {
            using container_type = void;
            using result_set_type = std::conditional_t<
                use_atomic, std::atomic<bool>, fake_atomic<bool>>;
            result_set_type result_set{false},
                pending_first_resumption{is_initially_suspended};
            coroutine_handle<> continuation;

            static constexpr bool is_initially_suspended = suspend_initial;
            static constexpr bool is_using_atomics = use_atomic;

            outcome_promise_type()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise constructed");
            }
            outcome_promise_type(const outcome_promise_type &) = delete;
            outcome_promise_type(outcome_promise_type &&) = delete;
            outcome_promise_type &
            operator=(const outcome_promise_type &) = delete;
            outcome_promise_type &operator=(outcome_promise_type &&) = delete;
            ~outcome_promise_type() = default;
            auto get_return_object()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise returns awaitable");
                return Awaitable{*this}; // could throw bad_alloc
            }
            void return_void() noexcept
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise returns void");
                MONAD_DEBUG_ASSERT(!result_set.load(std::memory_order_acquire));
                result_set.store(true, std::memory_order_release);
            }
            void unhandled_exception()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise unhandled exception");
                MONAD_DEBUG_ASSERT(!result_set.load(std::memory_order_acquire));
                std::rethrow_exception(std::current_exception()); // throws
            }
            auto initial_suspend() noexcept
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    this << " promise initial suspend = " << suspend_initial);
                struct awaiter
                {
                    constexpr bool await_ready() noexcept
                    {
                        return !suspend_initial;
                    }
                    void await_resume() noexcept {}
                    void await_suspend(coroutine_handle<> /*unused*/) noexcept
                    {
                    }
                };
                return awaiter{};
            }
            auto final_suspend() noexcept
            {
                struct awaiter
                {
                    // If we don't force a final suspend, promise will get
                    // deleted before awaitable
                    // TODO: Implement detachable awaitables
                    constexpr bool await_ready() noexcept
                    {
                        return false;
                    }
                    void await_resume() noexcept {}
    #if BOOST_OUTCOME_HAVE_NOOP_COROUTINE
                    coroutine_handle<> await_suspend(
                        coroutine_handle<outcome_promise_type> self) noexcept
                    {
                        if (self.promise().continuation) {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will resume "
                                   "coroutine "
                                << self.promise().continuation.address());
                        }
                        else {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will exit");
                        }
                        return self.promise().continuation
                                   ? self.promise().continuation
                                   : noop_coroutine();
                    }
    #else
                    void
                    await_suspend(coroutine_handle<outcome_promise_type> self)
                    {
                        if (self.promise().continuation) {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will resume "
                                   "coroutine "
                                << self.promise().continuation.address());
                            return self.promise().continuation.resume();
                        }
                        else {
                            BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                                &self.promise()
                                << " promise final suspend will exit");
                        }
                    }
    #endif
                };
                return awaiter{};
            }
        };
        template <class Awaitable, bool suspend_initial, bool use_atomic>
        constexpr inline auto move_result_from_promise_if_not_void(
            outcome_promise_type<Awaitable, suspend_initial, use_atomic, false>
                &p)
        {
            return static_cast<typename Awaitable::container_type &&>(p.result);
        }
        template <class Awaitable, bool suspend_initial, bool use_atomic>
        constexpr inline void move_result_from_promise_if_not_void(
            outcome_promise_type<Awaitable, suspend_initial, use_atomic, true>
                & /*unused*/)
        {
        }

        template <
            class Cont, class Executor, bool suspend_initial, bool use_atomic>
        struct BOOST_OUTCOME_NODISCARD awaitable
        {
            using container_type = Cont;
            using value_type = Cont;
            using executor_type = Executor;
            using promise_type = outcome_promise_type<
                awaitable, suspend_initial, use_atomic,
                std::is_void<container_type>::value>;
            coroutine_handle<promise_type> _h;

            awaitable(awaitable &&o) noexcept
                : _h(static_cast<coroutine_handle<promise_type> &&>(o._h))
            {
                o._h = nullptr;
            }
            awaitable(const awaitable &o) = delete;
            awaitable &operator=(awaitable &&) = delete; // as per P1056
            awaitable &operator=(const awaitable &) = delete;
            ~awaitable()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    &_h.promise() << " awaitable destructs");
                if (_h) {
                    _h.destroy();
                }
            }
            explicit awaitable(promise_type &p) // could throw
                : _h(coroutine_handle<promise_type>::from_promise(p))
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    &_h.promise()
                    << " awaitable constructs for coroutine " << _h.address()
                    << " shall resume on first suspend = "
                    << promise_type::is_initially_suspended);
            }
            bool valid() const noexcept
            {
                return _h != nullptr;
            }
            bool await_ready() noexcept
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    &_h.promise()
                    << " await_ready = "
                    << _h.promise().result_set.load(std::memory_order_acquire));
                return _h.promise().result_set.load(std::memory_order_acquire);
            }
            container_type await_resume()
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    &_h.promise() << " await_resume");
                MONAD_DEBUG_ASSERT(_h.promise().result_set.load(std::memory_order_acquire));
                if (!_h.promise().result_set.load(std::memory_order_acquire)) {
                    std::terminate();
                }
                return detail::move_result_from_promise_if_not_void(
                    _h.promise());
            }
    #if BOOST_OUTCOME_HAVE_NOOP_COROUTINE
            coroutine_handle<> await_suspend(coroutine_handle<> cont) noexcept
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    &_h.promise()
                    << " await_suspend suspends coroutine " << cont.address());
                auto &p = _h.promise();
                p.continuation = cont;
                bool expected = true;
                if (p.pending_first_resumption.compare_exchange_strong(
                        expected,
                        false,
                        std::memory_order_acq_rel,
                        std::memory_order_relaxed)) {
                    BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                        &_h.promise()
                        << " await_suspend does one time first resumption of "
                           "initially suspended coroutine "
                        << _h.address());
                    return _h;
                }
                return noop_coroutine();
            }
    #else
            void await_suspend(coroutine_handle<> cont)
            {
                BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                    &_h.promise()
                    << " await_suspend suspends coroutine " << cont.address());
                auto &p = _h.promise();
                p.continuation = cont;
                bool expected = true;
                if (p.pending_first_resumption.compare_exchange_strong(
                        expected,
                        false,
                        std::memory_order_acq_rel,
                        std::memory_order_relaxed)) {
                    BOOST_OUTCOME_V2_AWAITABLES_DEBUG_PRINTER(
                        &_h.promise()
                        << " await_suspend does one time first resumption of "
                           "initially suspended coroutine "
                        << _h.address());
                    _h.resume();
                }
            }
    #endif
        };
    }

    /*! AWAITING HUGO JSON CONVERSION TOOL
    SIGNATURE NOT RECOGNISED
    */
    template <class T, class Executor = void>
    using eager = detail::awaitable<T, Executor, false, false>;

    /*! AWAITING HUGO JSON CONVERSION TOOL
    SIGNATURE NOT RECOGNISED
    */
    template <class T, class Executor = void>
    using atomic_eager = detail::awaitable<T, Executor, false, true>;

    /*! AWAITING HUGO JSON CONVERSION TOOL
    SIGNATURE NOT RECOGNISED
    */
    template <class T, class Executor = void>
    using lazy = detail::awaitable<T, Executor, true, false>;

    /*! AWAITING HUGO JSON CONVERSION TOOL
    SIGNATURE NOT RECOGNISED
    */
    template <class T, class Executor = void>
    using atomic_lazy = detail::awaitable<T, Executor, true, true>;

}

#else

namespace awaitables = BOOST_OUTCOME_V2_NAMESPACE::awaitables;

#endif
