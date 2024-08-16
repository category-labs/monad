#pragma once

// Needs to come before others, on clang <stdatomic.h> breaks <atomic>
#include <atomic>

#include <liburing.h>

#include "all.h"
#include "executor.h"
#include "task.h"

#include <monad/context/config.h>

#include <memory>
#include <type_traits>

namespace monad
{
    namespace async
    {
        using BOOST_OUTCOME_V2_NAMESPACE::experimental::errc;

        struct executor_deleter
        {
            void operator()(monad_async_executor ex) const
            {
                to_result(monad_async_executor_destroy(ex)).value();
            }
        };

        using executor_ptr =
            std::unique_ptr<monad_async_executor_head, executor_deleter>;

        //! \brief Construct an executor instance, and return it in a smart
        //! pointer
        inline executor_ptr
        make_executor(struct monad_async_executor_attr &attr)
        {
            monad_async_executor ex;
            to_result(monad_async_executor_create(&ex, &attr)).value();
            return executor_ptr(ex);
        }

        struct file_deleter
        {
            monad_async_executor ex;

            constexpr file_deleter(monad_async_executor ex_)
                : ex(ex_)
            {
            }

            void operator()(monad_async_file f) const
            {
                to_result(
                    ::monad_async_task_file_destroy(
                        ex->current_task.load(std::memory_order_acquire), f))
                    .value();
            }
        };

        using file_ptr = std::unique_ptr<monad_async_file_head, file_deleter>;

        //! \brief Construct a file instance, and return it in a smart
        //! pointer
        inline file_ptr make_file(
            monad_async_task task, monad_async_file base, char const *subpath,
            struct open_how &how)
        {
            monad_async_file ex;
            to_result(
                monad_async_task_file_create(&ex, task, base, subpath, &how))
                .value();
            return file_ptr(
                ex,
                file_deleter{
                    task->current_executor.load(std::memory_order_acquire)});
        }

        struct socket_deleter
        {
            monad_async_executor ex;

            constexpr socket_deleter(monad_async_executor ex_)
                : ex(ex_)
            {
            }

            void operator()(monad_async_socket s) const
            {
                to_result(
                    monad_async_task_socket_destroy(
                        ex->current_task.load(std::memory_order_acquire), s))
                    .value();
            }
        };

        using socket_ptr =
            std::unique_ptr<monad_async_socket_head, socket_deleter>;

        //! \brief Construct a socket instance, and return it in a smart
        //! pointer
        inline socket_ptr make_socket(
            monad_async_task task, int domain, int type, int protocol,
            unsigned flags)
        {
            monad_async_socket ex;
            to_result(monad_async_task_socket_create(
                          &ex, task, domain, type, protocol, flags))
                .value();
            return socket_ptr(
                ex,
                socket_deleter{
                    task->current_executor.load(std::memory_order_acquire)});
        }

        struct task_deleter
        {
            void operator()(monad_async_task t) const
            {
                to_result(monad_async_task_destroy(t)).value();
            }
        };

        using task_ptr = std::unique_ptr<monad_async_task_head, task_deleter>;

        //! \brief Construct a task instance, and return it in a smart pointer
        inline task_ptr make_task(
            monad_context_switcher switcher, struct monad_async_task_attr &attr)
        {
            monad_async_task t;
            to_result(monad_async_task_create(&t, switcher, &attr)).value();
            return task_ptr(t);
        }

        struct work_dispatcher_deleter
        {
            void operator()(monad_async_work_dispatcher t) const
            {
                to_result(monad_async_work_dispatcher_destroy(t)).value();
            }
        };

        using work_dispatcher_ptr = std::unique_ptr<
            monad_async_work_dispatcher_head, work_dispatcher_deleter>;

        //! \brief Construct a work dispatcher instance, and return it in a
        //! smart pointer
        inline work_dispatcher_ptr
        make_work_dispatcher(struct monad_async_work_dispatcher_attr &attr)
        {
            monad_async_work_dispatcher t;
            to_result(monad_async_work_dispatcher_create(&t, &attr)).value();
            return work_dispatcher_ptr(t);
        }

        struct work_dispatcher_executor_deleter
        {
            void operator()(monad_async_work_dispatcher_executor t) const
            {
                to_result(monad_async_work_dispatcher_executor_destroy(t))
                    .value();
            }
        };

        using work_dispatcher_executor_ptr = std::unique_ptr<
            monad_async_work_dispatcher_executor_head,
            work_dispatcher_executor_deleter>;

        //! \brief Construct a work dispatcher executor instance, and return it
        //! in a smart pointer
        inline work_dispatcher_executor_ptr make_work_dispatcher_executor(
            monad_async_work_dispatcher dp,
            struct monad_async_work_dispatcher_executor_attr &attr)
        {
            monad_async_work_dispatcher_executor t;
            to_result(
                monad_async_work_dispatcher_executor_create(&t, dp, &attr))
                .value();
            return work_dispatcher_executor_ptr(t);
        }

        namespace detail
        {
            struct task_attach_impl_base
            {
                monad_async_executor ex;
                monad_async_task task;

            protected:
                constexpr task_attach_impl_base(
                    monad_async_executor ex_, monad_async_task task_)
                    : ex(ex_)
                    , task(task_)
                {
                }

                task_attach_impl_base(task_attach_impl_base &&o) noexcept
                    : ex(o.ex)
                    , task(o.task)
                {
                    o.ex = nullptr;
                    o.task = nullptr;
                }

            public:
                task_attach_impl_base(task_attach_impl_base const &) = delete;
                task_attach_impl_base &
                operator=(task_attach_impl_base const &) = delete;
                task_attach_impl_base &
                operator=(task_attach_impl_base &&) = delete;

                virtual ~task_attach_impl_base()
                {
                    if (task != nullptr) {
                        if (!monad_async_task_has_exited(task)) {
                            auto r =
                                to_result(monad_async_task_cancel(ex, task));
                            if (!r) {
                                if (r.assume_error() !=
                                    errc::resource_unavailable_try_again) {
                                    r.value();
                                }
                            }
                            while (!monad_async_task_has_exited(task)) {
                                to_result(
                                    monad_async_executor_run(ex, 1, nullptr))
                                    .value();
                            }
                        }
                        task->derived.user_code = nullptr;
                        task->derived.user_ptr = nullptr;
                    }
                }

                constexpr bool done() const noexcept
                {
                    return task != nullptr;
                }
            };

            template <class F>
            struct task_attach_impl final : public task_attach_impl_base
            {
                F f;

                constexpr task_attach_impl(
                    F &&f_, monad_async_executor ex, monad_async_task task)
                    : task_attach_impl_base(ex, task)
                    , f(std::forward<F>(f_))
                {
                }

                task_attach_impl(task_attach_impl &&) = default;

                static monad_c_result trampoline(monad_async_task task)
                {
                    auto *self = (task_attach_impl *)task->derived.user_ptr;
                    assert(task == self->task);
                    auto ret = self->f(task);
                    // self may be deleted at this point
                    task->derived.user_code = nullptr;
                    task->derived.user_ptr = nullptr;
                    return ret;
                }
            };
        }

        //! \brief Convenience attach of a C++ callable to a task.
        //! Destroying the returned type cancels the task and blocks until task
        //! exits.
        template <class F, class... Args>
            requires(
                std::is_invocable_v<F, monad_async_task_head *, Args...> &&
                std::is_constructible_v<
                    BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                        intptr_t>,
                    std::invoke_result_t<F, monad_async_task_head *, Args...>>)
        inline constexpr auto attach_to_executor(
            monad_async_executor ex, monad_async_task task, F &&f,
            Args &&...args)
        {
            assert(monad_async_task_has_exited(task));
            detail::task_attach_impl impl{
                [f = std::move(f), ... args = std::move(args)](
                    monad_async_task task) mutable -> monad_c_result {
                    BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                        intptr_t>
                        ret{f(task, std::move(args)...)};
                    // this may be deleted by now
                    return ret ? monad_c_make_success(ret.assume_value())
                               : monad_c_make_failure(
                                     (int)ret.assume_error().value());
                },
                ex,
                task};
            using impl_type = std::decay_t<decltype(impl)>;
            task->derived.user_code = impl_type::trampoline;
            auto ret =
                std::unique_ptr<impl_type>(new impl_type(std::move(impl)));
            task->derived.user_ptr = ret.get();
            to_result(monad_async_task_attach(ex, task, nullptr)).value();
            return ret;
        }
    }
}
