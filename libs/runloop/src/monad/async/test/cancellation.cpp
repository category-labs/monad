#include <gtest/gtest.h>

#include "../../test_common.hpp"

#include <monad/async/cpp_helpers.hpp>
#include <monad/async/executor.h>
#include <monad/async/socket_io.h>
#include <monad/async/task.h>
#include <monad/config.h>
#include <monad/context/config.h>
#include <monad/context/context_switcher.h>
#include <monad/util/temp_files.h>

#include <monad/core/assert.h>
#include <monad/core/scope_polyfill.hpp>
#include <monad/core/small_prng.hpp>

#include <boost/outcome/config.hpp>
#include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#include <boost/outcome/experimental/status-code/status-code/iostream_support.hpp>
#include <boost/outcome/experimental/status-code/status-code/status_error.hpp>
#include <boost/outcome/iostream_support.hpp>

#include <atomic>
#include <chrono>
#include <list>

#include <sys/socket.h>
#include <type_traits>

#include <netinet/in.h>

/* Notes on weird io_uring socket recv hang:

- The task which gets stuck I notice successfully connects without any apparent
matching accept by the setup task. None of the read i/o it schedules against the
connection fail. This is why it hangs forever, it looks like a successful
connection in every way, and reads against it never fail and never complete.

- The CQE which says that the connect succeeded returns res=0 exactly the same
as any other connect. We cannot disambiguate correct connections from zombie
ones this way.

- I've added a one second initial timeout to work around this. If a single
completion turns up, we're good. If not one appears in one second, we assume
we have a zombie connection - we cancel all the read i/o we initiated, and
hard close the socket.

- My best guess is that this is a bug in io_uring in kernel 6.8. It doesn't
happen with syscall connect, and I'd guess most production code will have
dead connection detection and handling so it probably didn't get noticed until
later.
*/

#pragma GCC diagnostic ignored "-Winvalid-offsetof"

static inline monad_c_result null_setup(monad_async_task, bool const &, int &)
{
    return monad_c_make_success(0);
}

template <class F, class G = decltype(null_setup)>
    requires(
        std::is_invocable_r_v<
            monad_c_result, F, monad_async_task, bool const &, int &> &&
        std::is_invocable_r_v<
            monad_c_result, G, monad_async_task, bool const &, int &>)
static void test_cancellation(
    char const *desc, monad_async_executor_attr ex_attr, F &&op,
    G &&setup_task_impl = null_setup)
{
    {
        auto ex = make_executor(ex_attr);
        auto switcher = make_context_switcher(monad_context_switcher_fcontext);

        struct shared_t
        {
            F &op;
            G &setup;
            bool done{false};
            int failures{0};
            uint32_t ops{0};
        } shared{op, setup_task_impl};

        monad_async_task_attr task_attr{};
        task_ptr setup_task = make_task(switcher.get(), task_attr);
        setup_task->derived.user_code =
            +[](monad_context_task task_) -> monad_c_result {
            auto *task = (monad_async_task)task_;
            auto *shared = (shared_t *)task->derived.user_ptr;
            return shared->setup(task, shared->done, shared->failures);
        };
        setup_task->derived.user_ptr = &shared;
        to_result(monad_async_task_attach(ex.get(), setup_task.get(), nullptr))
            .value();
        // Set to highest priority to maximise new connections listened
        to_result(monad_async_task_set_priorities(
                      setup_task.get(),
                      monad_async_priority_high,
                      monad_async_priority_unchanged))
            .value();

        auto task_impl = +[](monad_context_task task_) -> monad_c_result {
            auto *task = (monad_async_task)task_;
            auto *shared = (shared_t *)task->derived.user_ptr;
            while (!shared->done) {
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    shared->op(task, shared->done, shared->failures));
                shared->ops++;
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
            }
            MONAD_ASSERT(task->io_submitted == 0);
            MONAD_ASSERT(task->io_completed_not_reaped == 0);
            return monad_c_make_success(0);
        };

        std::vector<task_ptr> tasks;
        tasks.reserve(ex_attr.io_uring_ring.entries + 8);
        for (size_t n = 0; n < tasks.capacity(); n++) {
            tasks.push_back(make_task(switcher.get(), task_attr));
            tasks.back()->derived.user_code = task_impl;
            tasks.back()->derived.user_ptr = &shared;
            to_result(
                monad_async_task_attach(ex.get(), tasks.back().get(), nullptr))
                .value();
            // Run at lowest priority
            to_result(monad_async_task_set_priorities(
                          tasks.back().get(),
                          monad_async_priority_low,
                          monad_async_priority_unchanged))
                .value();
        }

        monad::small_prng rand;
        (void)rand;

        const struct timespec nowait = {};

        std::cout << time(nullptr) << ": Beginning testing " << desc
                  << " for correctness in cancellation for three seconds ..."
                  << std::endl;
        uint32_t implicit_cancels = 0, explicit_cancels = 0;
        auto const begin = std::chrono::steady_clock::now();
        do {
            auto const v = rand();
            task_ptr &i = tasks[v % tasks.size()];
            assert(i);
            // Before cancelling it, raise to highest priority otherwise other
            // tasks can swamp this task
            to_result(monad_async_task_set_priorities(
                          i.get(),
                          monad_async_priority_high,
                          monad_async_priority_unchanged))
                .value();
            if ((v >> 29) == 0) {
                // Implicit cancellation
                // std::cout << time(nullptr) << ": Implicitly cancelling "
                //          << i.get() << std::endl;
                i.reset();
                implicit_cancels++;
            }
            else {
                // Explicit cancellation
                // std::cout << time(nullptr) << ": Explicitly cancelling "
                //          << i.get() << std::endl;
                auto r = to_result(monad_async_task_cancel(ex.get(), i.get()));
                if (!r) {
                    if (r.assume_error() !=
                        errc::resource_unavailable_try_again) {
                        r.value();
                    }
                }
                while (!monad_async_task_has_exited(i.get())) {
                    monad_async_task_debug_validate(i.get());
                    auto r = to_result(monad_async_executor_run(
                        ex.get(), size_t(-1), &nowait));
                    if (!r && r.assume_error() != errc::stream_timeout) {
                        r.value();
                    }
                    if (std::chrono::steady_clock::now() - begin >
                        std::chrono::seconds(10)) {
                        std::cerr << "Task " << i.get()
                                  << " did not exit after cancellation in a "
                                     "timely fashion!"
                                  << std::endl;
                        abort();
                    }
                }
                explicit_cancels++;
                // std::cout << time(nullptr) << ": Replacing cancelled "
                //           << i.get() << std::endl;
            }
            i = make_task(switcher.get(), task_attr);
            i->derived.user_code = task_impl;
            i->derived.user_ptr = &shared;
            to_result(monad_async_task_attach(ex.get(), i.get(), nullptr))
                .value();
            auto r = to_result(
                monad_async_executor_run(ex.get(), size_t(-1), &nowait));
            if (!r && r.assume_error() != errc::stream_timeout) {
                r.value();
            }
        }
        while (std::chrono::steady_clock::now() - begin <
               std::chrono::seconds(3));
        std::cout << "\n"
                  << time(nullptr)
                  << ": Stopping initiating new i/o and cancellations (i/o "
                     "buffer deadlocks = "
                  << ex->registered_buffers.total_deadlocks_broken << ") ..."
                  << std::endl;
        shared.done = true;
        struct timespec ts = {.tv_sec = 1, .tv_nsec = 0};
        bool need_to_cancel_everything = false;
        while (monad_async_executor_has_work(ex.get())) {
            auto r =
                to_result(monad_async_executor_run(ex.get(), size_t(-1), &ts));
            if (std::chrono::steady_clock::now() - begin >
                std::chrono::seconds(9)) {
                break;
            }
            if (!r) {
                if (r.assume_error() != errc::stream_timeout) {
                    r.value();
                }
            }
        }
        std::cout << "\n"
                  << time(nullptr) << ": Six seconds later and "
                  << monad_async_executor_task_count(ex.get())
                  << " tasks are still going." << std::endl;
        if (!monad_async_task_has_exited(setup_task.get())) {
            std::cout << "\n"
                      << time(nullptr) << ": Cancelling setup task ..."
                      << std::endl;
            auto r =
                to_result(monad_async_task_cancel(ex.get(), setup_task.get()));
            if (!r) {
                if (r.assume_error() != errc::resource_unavailable_try_again) {
                    r.value();
                }
            }
        }
        while (monad_async_executor_has_work(ex.get())) {
            auto r =
                to_result(monad_async_executor_run(ex.get(), size_t(-1), &ts));
            if (std::chrono::steady_clock::now() - begin >
                std::chrono::seconds(10)) {
                need_to_cancel_everything = true;
                break;
            }
            if (!r) {
                if (r.assume_error() != errc::stream_timeout) {
                    r.value();
                }
            }
        }
        if (need_to_cancel_everything) {
            std::cout << "\n"
                      << time(nullptr)
                      << ": As buffer deadlock probably has occurred (i/o "
                         "buffer deadlocks = "
                      << ex->registered_buffers.total_deadlocks_broken
                      << "), cancelling "
                      << monad_async_executor_task_count(ex.get())
                      << " remaining tasks to speed up teardown ..."
                      << std::endl;
            /* The algorithm for breaking stuck read buffers deadlock is very
            slow as the timer breaking the deadlock fires every half second.
            The deadlock occurs very rarely, so the test suite will pass 99%
            of the time which makes that rare occurances into a sporadic CI
            failure. To avoid that, if we didn't exit above after seven seconds,
            we aggressively cancel all tasks to hurry things up.
            */
            for (auto &i : tasks) {
                if (!monad_async_task_has_exited(i.get())) {
                    auto r =
                        to_result(monad_async_task_cancel(ex.get(), i.get()));
                    if (!r) {
                        if (r.assume_error() !=
                            errc::resource_unavailable_try_again) {
                            r.value();
                        }
                    }
                }
            }
            while (monad_async_executor_has_work(ex.get())) {
                auto r = to_result(
                    monad_async_executor_run(ex.get(), size_t(-1), &ts));
                if (std::chrono::steady_clock::now() - begin >
                    std::chrono::seconds(20)) {
                    auto const *desc =
                        (char const *)to_result(
                            monad_async_executor_debug_string(ex.get()))
                            .value();
                    std::cout << "\n"
                              << time(nullptr)
                              << ": Running executor after requesting quit and "
                                 "force cancelling all tasks has "
                                 "failed. Internal debug for the executor is:\n"
                              << desc << std::endl;
                    free((void *)desc);
                    abort();
                }
                if (!r) {
                    if (r.assume_error() != errc::stream_timeout) {
                        r.value();
                    }
                }
            }
        }
        setup_task.reset();
        EXPECT_GT(shared.ops, 0);
        EXPECT_GT(implicit_cancels, 0);
        EXPECT_GT(explicit_cancels, 0);
        std::cout << time(nullptr) << ": Testing of " << desc
                  << " for correctness in cancellation complete. Did "
                  << shared.ops << " successful ops, " << implicit_cancels
                  << " implicit cancels, " << explicit_cancels
                  << " explicit cancels, " << ex->total_io_submitted
                  << " i/o submitted and " << ex->total_io_completed
                  << " i/o completed. " << ex->registered_buffers.total_released
                  << " registered i/o buffers were used, and "
                  << ex->registered_buffers.total_deadlocks_broken
                  << " i/o buffer deadlocks were broken." << std::endl;
        EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
        EXPECT_EQ(
            ex->registered_buffers.total_claimed,
            ex->registered_buffers.total_released);
        EXPECT_EQ(shared.failures, 0);
    }
    std::cout << "Testing of " << desc
              << " for correctness in cancellation has torn down everything "
                 "successfully."
              << std::endl;
}

TEST(cancellation, yield)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 16;
    ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
    test_cancellation(
        "yield",
        ex_attr,
        [](monad_async_task task, bool const &, int &) -> monad_c_result {
            monad_c_result r =
                monad_async_task_suspend_for_duration(nullptr, task, 0);
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                if (outcome_status_code_equal_generic(&r.error, ETIME)) {
                    return monad_c_make_success(0);
                }
            }
            return r;
        });
}

TEST(cancellation, suspend_for_duration)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 16;
    ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
    test_cancellation(
        "suspend for duration",
        ex_attr,
        [](monad_async_task task, bool const &, int &) -> monad_c_result {
            monad_c_result r = monad_async_task_suspend_for_duration(
                nullptr, task, 1000000ULL); // 1 millisecond
            if (BOOST_OUTCOME_C_RESULT_HAS_ERROR(r)) {
                if (outcome_status_code_equal_generic(&r.error, ETIME)) {
                    return monad_c_make_success(0);
                }
            }
            return r;
        });
}

TEST(cancellation, file_open_close)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 16;
    ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
    ex_attr.io_uring_wr_ring.entries = 16;
    test_cancellation(
        "file open close",
        ex_attr,
        [](monad_async_task task, bool const &, int &) -> monad_c_result {
            try {
                struct open_how how = {
                    .flags = O_RDWR, .mode = 0, .resolve = 0};
                char tempfilepath[256];
                close(monad_make_temporary_file(
                    tempfilepath, sizeof(tempfilepath)));
                auto fh = make_file(task, nullptr, tempfilepath, how);
                unlink(tempfilepath);
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    monad_async_task_file_fallocate(
                        task, fh.get(), 0, 0, 1024));
                fh.reset();
                return monad_c_make_success(0);
            }
            catch (const BOOST_OUTCOME_V2_NAMESPACE::experimental::status_error<
                   BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code::
                       domain_type> &e) {
                return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, e.code());
            }
            catch (...) {
                abort();
            }
        });
}

TEST(cancellation, socket_open_close)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 16;
    ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
    test_cancellation(
        "socket open close",
        ex_attr,
        [](monad_async_task task, bool const &, int &) -> monad_c_result {
            try {
                // Open a listening socket
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);

                struct sockaddr_in localhost = {
                    .sin_family = AF_INET,
                    .sin_port = 0 /* any */,
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)},
                    .sin_zero = {}};

                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(monad_async_task_socket_bind(
                    sock.get(), (sockaddr *)&localhost, sizeof(localhost)));
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    monad_async_task_socket_listen(sock.get(), 0));
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    monad_async_task_socket_transfer_to_uring(
                        task, sock.get()));
                sock.reset();
                return monad_c_make_success(0);
            }
            catch (const BOOST_OUTCOME_V2_NAMESPACE::experimental::status_error<
                   BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code::
                       domain_type> &e) {
                return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, e.code());
            }
            catch (...) {
                abort();
            }
        });
}

// Note that this test intentionally causes buffer allocation deadlock as much
// as possible to test the buffer deadlock handling code.
TEST(cancellation, file_read)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 16;
    ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
    ex_attr.io_uring_wr_ring.entries = 16;
    test_cancellation(
        "file read",
        ex_attr,
        [](monad_async_task task,
           bool const &done,
           int &failures) -> monad_c_result {
            std::array<
                std::pair<
                    monad_async_io_status,
                    monad_async_task_registered_io_buffer>,
                1000>
                iostatuses;
            auto uniostatuses = monad::make_scope_exit([&]() noexcept {
                for (auto &i : iostatuses) {
                    if (i.second.index != 0) {
                        std::cerr << "FAILURE: i.second.index !=0, instead is "
                                  << (i.second.index - 1) << " "
                                  << i.second.iov[0].iov_base << std::endl;
                        failures++;
                    }
                }
            });
            auto process_completion =
                [&](monad_async_io_status *completed) -> bool {
                if (completed == nullptr) {
                    return false;
                }
                auto *i = (std::pair<
                           monad_async_io_status,
                           monad_async_task_registered_io_buffer> *)completed;
                auto r = to_result(completed->result);
                if (!r) {
                    // No i/o buffer must be allocated if the op fails
                    MONAD_ASSERT(i->second.index == 0);
                    MONAD_ASSERT(i->second.iov[0].iov_base == nullptr);
                    MONAD_ASSERT(i->second.iov[0].iov_len == 0);
                    if (r.assume_error() == errc::operation_canceled) {
                        return true;
                    }
                    if (r.assume_error() == errc::no_buffer_space) {
                        return false;
                    }
                    CHECK_RESULT(completed->result);
                }
                CHECK_RESULT(monad_async_task_release_registered_io_buffer(
                    task, i->second.index));
                i->second.index = 0;
                return false;
            };
            auto empty_completions = [&] {
                for (;;) {
                    monad_async_io_status *completed = nullptr;
                    auto r =
                        to_result(monad_async_task_suspend_until_completed_io(
                            &completed,
                            task,
                            monad_async_duration_infinite_non_cancelling));
                    if (!r) {
                        MONAD_ASSERT(r.assume_error() != errc::stream_timeout);
                        MONAD_ASSERT(
                            r.assume_error() != errc::operation_canceled);
                        std::cerr << "###### "
                                  << r.assume_error().message().c_str()
                                  << std::endl;
                        r.value();
                    }
                    if (completed == nullptr) {
                        return r.value() > 0;
                    }
                    process_completion(completed);
                }
            };
            try {
                struct open_how how = {
                    .flags = O_RDWR, .mode = 0, .resolve = 0};
                char tempfilepath[256];
                close(monad_make_temporary_file(
                    tempfilepath, sizeof(tempfilepath)));
                auto fh = make_file(task, nullptr, tempfilepath, how);
                unlink(tempfilepath);
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    monad_async_task_file_fallocate(
                        task, fh.get(), 0, 0, 1024));
                try {
                    size_t when_done_became_set = size_t(-1);
                    for (size_t n = 0; n < iostatuses.size(); n++) {
                        if (done) {
                            if (when_done_became_set == size_t(-1)) {
                                when_done_became_set = n;
                            }
                            if (n - when_done_became_set > 20) {
                                // Test can take too long to exit otherwise
                                break;
                            }
                            std::cout << time(nullptr) << ": Task " << task
                                      << " initiates i/o "
                                      << &iostatuses[n].first << " (" << n
                                      << "/" << iostatuses.size() << ")"
                                      << std::endl;
                        }
                        memset(
                            &iostatuses[n].second,
                            0,
                            sizeof(iostatuses[n].second));
                        monad_async_task_file_read(
                            &iostatuses[n].first,
                            task,
                            fh.get(),
                            &iostatuses[n].second,
                            1,
                            n,
                            0);
                        if (process_completion(
                                monad_async_task_completed_io(task))) {
                            // Cancelled
                            break;
                        }
                    }
                    if (done) {
                        std::cout << time(nullptr) << ": Task " << task
                                  << " stops initiating new i/o and starts "
                                     "emptying remaining i/o."
                                  << std::endl;
                    }
                }
                catch (
                    const BOOST_OUTCOME_V2_NAMESPACE::experimental::
                        status_error<BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                         posix_code::domain_type> &e) {
                    std::cout
                        << "NOTE: C++ exception thrown during i/o dispatch: "
                        << e.what() << std::endl;
                    while (empty_completions())
                        ;
                    MONAD_ASSERT(
                        task->io_submitted + task->io_completed_not_reaped ==
                        0);
                    fh.reset();
                    return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                        monad, e.code());
                }
                while (empty_completions())
                    ;
                if (done) {
                    std::cout << time(nullptr) << ": Task " << task
                              << " completes emptying remaining i/o and exits."
                              << std::endl;
                }
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
                fh.reset();
                return monad_c_make_success(0);
            }
            catch (const BOOST_OUTCOME_V2_NAMESPACE::experimental::status_error<
                   BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code::
                       domain_type> &e) {
                while (empty_completions())
                    ;
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
                return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, e.code());
            }
            catch (...) {
                abort();
            }
        });
}

TEST(cancellation, file_write)
{
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 16;
    ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
    ex_attr.io_uring_wr_ring.entries = 16;
    ex_attr.io_uring_wr_ring.registered_buffers.small_count = 64;
    test_cancellation(
        "file write",
        ex_attr,
        [](monad_async_task task,
           bool const &done,
           int &failures) -> monad_c_result {
            std::array<
                std::pair<
                    monad_async_io_status,
                    monad_async_task_registered_io_buffer>,
                1000>
                iostatuses;
            auto uniostatuses = monad::make_scope_exit([&]() noexcept {
                for (auto &i : iostatuses) {
                    if (i.second.index != 0) {
                        std::cerr << "FAILURE: i.second.index !=0, instead is "
                                  << (i.second.index - 1) << " "
                                  << i.second.iov[0].iov_base << std::endl;
                        failures++;
                    }
                }
            });
            auto process_completion =
                [&](monad_async_io_status *completed) -> bool {
                if (completed == nullptr) {
                    return false;
                }
                auto *i = (std::pair<
                           monad_async_io_status,
                           monad_async_task_registered_io_buffer> *)completed;
                MONAD_ASSERT(i->second.index != 0);
                CHECK_RESULT(monad_async_task_release_registered_io_buffer(
                    task, i->second.index));
                i->second.index = 0;
                auto r = to_result(completed->result);
                if (!r) {
                    if (r.assume_error() == errc::operation_canceled) {
                        return true;
                    }
                    if (r.assume_error() == errc::no_buffer_space) {
                        return false;
                    }
                    CHECK_RESULT(completed->result);
                }
                return false;
            };
            auto empty_completions = [&] {
                for (;;) {
                    monad_async_io_status *completed = nullptr;
                    auto r =
                        to_result(monad_async_task_suspend_until_completed_io(
                            &completed,
                            task,
                            monad_async_duration_infinite_non_cancelling));
                    if (!r) {
                        MONAD_ASSERT(r.assume_error() != errc::stream_timeout);
                        MONAD_ASSERT(
                            r.assume_error() != errc::operation_canceled);
                        std::cerr << "###### "
                                  << r.assume_error().message().c_str()
                                  << std::endl;
                        r.value();
                    }
                    if (completed == nullptr) {
                        return r.value() > 0;
                    }
                    process_completion(completed);
                }
            };
            try {
                struct open_how how = {
                    .flags = O_RDWR, .mode = 0, .resolve = 0};
                char tempfilepath[256];
                close(monad_make_temporary_file(
                    tempfilepath, sizeof(tempfilepath)));
                auto fh = make_file(task, nullptr, tempfilepath, how);
                unlink(tempfilepath);
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    monad_async_task_file_fallocate(
                        task, fh.get(), 0, 0, 1024));
                try {
                    size_t when_done_became_set = size_t(-1);
                    for (size_t n = 0; n < iostatuses.size(); n++) {
                        if (done) {
                            if (when_done_became_set == size_t(-1)) {
                                when_done_became_set = n;
                            }
                            if (n - when_done_became_set > 20) {
                                // Test can take too long to exit otherwise
                                break;
                            }
                            std::cout << time(nullptr) << ": Task " << task
                                      << " initiates i/o "
                                      << &iostatuses[n].first << " (" << n
                                      << "/" << iostatuses.size() << ")"
                                      << std::endl;
                        }
                        memset(
                            &iostatuses[n].second,
                            0,
                            sizeof(iostatuses[n].second));
                        auto r = to_result(
                            monad_async_task_claim_registered_file_io_write_buffer(
                                &iostatuses[n].second,
                                task,
                                1,
                                {.fail_dont_suspend = true,
                                 ._for_read_ring = false}));
                        if (!r) {
                            MONAD_ASSERT(iostatuses[n].second.index == 0);
                            if (r.assume_error() == errc::operation_canceled) {
                                // Cancelled
                                break;
                            }
                            if (r.assume_error() != errc::no_buffer_space) {
                                r.value();
                            }
                            n--;
                            // Let other tasks potentially run
                            monad_async_io_status *completed = nullptr;
                            r = to_result(monad_async_task_suspend_for_duration(
                                &completed, task, 0));
                            if (!r) {
                                if (r.assume_error() ==
                                    errc::operation_canceled) {
                                    // Cancelled
                                    break;
                                }
                                else if (
                                    r.assume_error() != errc::stream_timeout) {
                                    r.value();
                                }
                            }
                        }
                        else {
                            MONAD_ASSERT(iostatuses[n].second.index != 0);
                            iostatuses[n].second.iov[0].iov_len = 1;
                            monad_async_task_file_write(
                                &iostatuses[n].first,
                                task,
                                fh.get(),
                                iostatuses[n].second.index,
                                iostatuses[n].second.iov,
                                1,
                                n,
                                0);
                        }
                        if (process_completion(
                                monad_async_task_completed_io(task))) {
                            // Cancelled
                            break;
                        }
                    }
                    if (done) {
                        std::cout << time(nullptr) << ": Task " << task
                                  << " stops initiating new i/o and starts "
                                     "emptying remaining i/o."
                                  << std::endl;
                    }
                }
                catch (
                    const BOOST_OUTCOME_V2_NAMESPACE::experimental::
                        status_error<BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                         posix_code::domain_type> &e) {
                    std::cout
                        << "NOTE: C++ exception thrown during i/o dispatch: "
                        << e.what() << std::endl;
                    while (empty_completions())
                        ;
                    return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                        monad, e.code());
                }
                while (empty_completions())
                    ;
                if (done) {
                    std::cout << time(nullptr) << ": Task " << task
                              << " completes emptying remaining i/o and exits."
                              << std::endl;
                }
                fh.reset();
                return monad_c_make_success(0);
            }
            catch (const BOOST_OUTCOME_V2_NAMESPACE::experimental::status_error<
                   BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code::
                       domain_type> &e) {
                return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, e.code());
            }
            catch (...) {
                abort();
            }
        });
}

TEST(cancellation, socket_read)
{
    static struct sockaddr_in server_socket;
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 16;
    ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
    ex_attr.io_uring_ring.registered_buffers.small_kernel_allocated_count =
        64 + 4;
    test_cancellation(
        "socket read",
        ex_attr,
        [](monad_async_task task,
           bool const &done,
           int &failures) -> monad_c_result {
            auto print_on_exit = monad::make_scope_exit([&]() noexcept {
                if (done) {
                    std::cout << time(nullptr) << ": Task " << task << " exits."
                              << std::endl;
                }
            });
            try {
                auto sock = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);
                to_result(
                    monad_async_task_socket_transfer_to_uring(task, sock.get()))
                    .value();
                {
                    monad_async_io_status status{};
                    monad_async_task_socket_connect(
                        &status,
                        task,
                        sock.get(),
                        (const struct sockaddr *)&server_socket,
                        sizeof(server_socket));
                    monad_async_io_status *completed;
                    auto r =
                        to_result(monad_async_task_suspend_until_completed_io(
                            &completed,
                            task,
                            monad_async_duration_infinite_cancelling));
                    if (!r) {
                        if (r.assume_error() == errc::operation_canceled) {
                            // Cancel the connect
                            r = to_result(
                                monad_async_task_io_cancel(task, &status));
                            for (;;) {
                                if (done) {
                                    std::cout << time(nullptr) << ": Task "
                                              << task
                                              << " sees connect cancelled. "
                                                 "io_submitted="
                                              << task->io_submitted
                                              << " io_completed_not_reaped="
                                              << task->io_completed_not_reaped
                                              << std::endl;
                                }
                                r = to_result(
                                    monad_async_task_suspend_until_completed_io(
                                        &completed,
                                        task,
                                        monad_async_duration_infinite_non_cancelling));
                                if (completed == nullptr) {
                                    break;
                                }
                            }
                            sock.reset();
                            return monad_c_make_success(0);
                        }
                    }
                    r = to_result(status.result);
                    if (!r) {
                        std::cerr << "Socket connect failed with: "
                                  << r.assume_error().message().c_str()
                                  << std::endl;
                        r.value();
                    }
                }
                if (done) {
                    std::cout << time(nullptr) << ": Task " << task
                              << " successfully connects on port "
                              << ((sockaddr_in *)&sock->addr)->sin_port
                              << std::endl;
                }

                std::array<
                    std::pair<
                        monad_async_io_status,
                        monad_async_task_registered_io_buffer>,
                    1000>
                    iostatuses;
                auto uniostatuses = monad::make_scope_exit([&]() noexcept {
                    for (auto &i : iostatuses) {
                        if (i.second.index != 0) {
                            std::cerr
                                << "FAILURE: i.second.index !=0, instead is "
                                << (i.second.index - 1) << " "
                                << i.second.iov[0].iov_base << std::endl;
                            failures++;
                        }
                    }
                });
                size_t completions_processed = 0;
                auto process_completion =
                    [&](monad_async_io_status *completed) -> bool {
                    if (completed == nullptr) {
                        return false;
                    }
                    auto *i =
                        (std::pair<
                            monad_async_io_status,
                            monad_async_task_registered_io_buffer> *)completed;
                    auto r = to_result(completed->result);
                    if (!r) {
                        // No i/o buffer must be allocated if the op fails
                        MONAD_ASSERT(i->second.index == 0);
                        MONAD_ASSERT(i->second.iov[0].iov_base == nullptr);
                        MONAD_ASSERT(i->second.iov[0].iov_len == 0);
                        if (r.assume_error() == errc::operation_canceled) {
                            return true;
                        }
                        if (r.assume_error() == errc::connection_reset) {
                            return true;
                        }
                        if (r.assume_error() == errc::no_buffer_space) {
                            return false;
                        }
                        CHECK_RESULT(completed->result);
                    }
                    if (i->second.index != 0) {
                        completions_processed++;
                        CHECK_RESULT(
                            monad_async_task_release_registered_io_buffer(
                                task, i->second.index));
                    }
                    i->second.index = 0;
                    return false;
                };
                // Returns true if there are completions yet to reap
                auto empty_completions_non_cancelling = [&] {
                    for (;;) {
                        monad_async_io_status *completed = nullptr;
                        auto r = to_result(
                            monad_async_task_suspend_until_completed_io(
                                &completed,
                                task,
                                monad_async_duration_infinite_non_cancelling));
                        if (!r) {
                            MONAD_ASSERT(
                                r.assume_error() != errc::stream_timeout);
                            MONAD_ASSERT(
                                r.assume_error() != errc::operation_canceled);
                            std::cerr << "###### "
                                      << r.assume_error().message().c_str()
                                      << std::endl;
                            r.value();
                        }
                        if (done) {
                            std::cout
                                << time(nullptr) << ": Task " << task
                                << " is emptying remaining i/o. io_submitted="
                                << task->io_submitted
                                << " io_completed_not_reaped="
                                << task->io_completed_not_reaped
                                << " completed=" << completed
                                << " r.value()=" << r.value() << std::endl;
                        }
                        if (completed == nullptr) {
                            return r.value() > 0;
                        }
                        process_completion(completed);
                    }
                };
                // Returns -1 if we have been cancelled, 0 if no more work
                auto empty_completions_cancelling = [&] -> long {
                    for (;;) {
                        monad_async_io_status *completed = nullptr;
                        auto r = to_result(
                            monad_async_task_suspend_until_completed_io(
                                &completed,
                                task,
                                monad_async_duration_infinite_cancelling));
                        if (!r) {
                            MONAD_ASSERT(
                                r.assume_error() != errc::stream_timeout);
                            if (r.assume_error() == errc::operation_canceled) {
                                return -1;
                            }
                            r.value();
                        }
                        if (done) {
                            std::cout
                                << time(nullptr) << ": Task " << task
                                << " is emptying remaining i/o. io_submitted="
                                << task->io_submitted
                                << " io_completed_not_reaped="
                                << task->io_completed_not_reaped
                                << " completed=" << completed
                                << " r.value()=" << r.value() << std::endl;
                        }
                        if (completed == nullptr) {
                            return r.value();
                        }
                        process_completion(completed);
                    }
                };
                auto shutdown_socket = [&] {
                    MONAD_ASSERT(
                        task->io_submitted + task->io_completed_not_reaped ==
                        0);
                    monad_async_io_status status{};
                    monad_async_task_socket_shutdown(
                        &status, task, sock.get(), SHUT_RDWR);
                    for (;;) {
                        monad_async_io_status *completed = nullptr;
                        auto r = to_result(
                            monad_async_task_suspend_until_completed_io(
                                &completed,
                                task,
                                monad_async_duration_infinite_non_cancelling));
                        if (!r) {
                            std::cerr << "Socket shutdown failed with: "
                                      << r.assume_error().message().c_str()
                                      << std::endl;
                            r.value();
                        }
                        if (completed == &status) {
                            break;
                        }
                    }
                    while (empty_completions_non_cancelling())
                        ;
                };
                try {
                    size_t when_done_became_set = size_t(-1);
                    for (size_t n = 0; n < iostatuses.size(); n++) {
                        if (done) {
                            if (when_done_became_set == size_t(-1)) {
                                when_done_became_set = n;
                            }
                            if (n - when_done_became_set > 20) {
                                // Test can take too long to exit otherwise
                                break;
                            }
                            std::cout << time(nullptr) << ": Task " << task
                                      << " initiates i/o "
                                      << &iostatuses[n].first << " (" << n
                                      << "/" << iostatuses.size() << ")"
                                      << std::endl;
                        }
                        memset(
                            &iostatuses[n].second,
                            0,
                            sizeof(iostatuses[n].second));
                        monad_async_task_socket_receive(
                            &iostatuses[n].first,
                            task,
                            sock.get(),
                            &iostatuses[n].second,
                            1,
                            0);
                        if (process_completion(
                                monad_async_task_completed_io(task))) {
                            // Cancelled
                            break;
                        }
                    }
                    if (done) {
                        std::cout << time(nullptr) << ": Task " << task
                                  << " stops initiating new i/o and starts "
                                     "emptying remaining i/o. io_submitted="
                                  << task->io_submitted
                                  << " io_completed_not_reaped="
                                  << task->io_completed_not_reaped << std::endl;
                    }
                }
                catch (
                    const BOOST_OUTCOME_V2_NAMESPACE::experimental::
                        status_error<BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                         posix_code::domain_type> &e) {
                    std::cout << "NOTE: C++ exception thrown during i/o "
                                 "dispatch in task "
                              << task << ": " << e.what() << std::endl;
                    while (empty_completions_cancelling() > 0)
                        ;
                    shutdown_socket();
                    MONAD_ASSERT(
                        task->io_submitted + task->io_completed_not_reaped ==
                        0);
                    sock.reset();
                    MONAD_ASSERT(
                        task->io_submitted + task->io_completed_not_reaped ==
                        0);
                    return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                        monad, e.code());
                }
                if (completions_processed == 0) {
                    /* I discovered "the hard way" that under load, connect
                    will complete without error but you've actually got
                    yourself a zombie connection. I confirmed this by matching
                    server task accepts to client task connects, and yeah it
                    literally spuriously returns a successful connect sometimes.
                    Best of all, reads on said zombie connection don't fail, in
                    fact absolutely nothing happens at all and your task just
                    hangs. I'm going to assume this is some sort of bug in my
                    kernel's io_uring, because syscall connect does not behave
                    this way.

                    We work around this by initially suspending for one second.
                    If not a single completion arrives, we assume we have a
                    zombie connection and exit immediately.
                    */
                    if (done) {
                        std::cout
                            << time(nullptr) << ": Task " << task
                            << " awaits any completion at all to detect a dead "
                               "socket ..."
                            << std::endl;
                    }
                    monad_async_io_status *completed = nullptr;
                    auto r =
                        to_result(monad_async_task_suspend_until_completed_io(
                            &completed, task, 1000000000));
                    if (completed == nullptr) {
                        std::cerr << "NOTE: Task " << task
                                  << " appears to have been given a zombie "
                                     "connection, cancelling all the i/o "
                                     "and resetting the task!"
                                  << std::endl;
                        for (auto &i : iostatuses) {
                            r = to_result(
                                monad_async_task_io_cancel(task, &i.first));
                        }
                        while (empty_completions_non_cancelling())
                            ;
                        MONAD_ASSERT(
                            task->io_submitted +
                                task->io_completed_not_reaped ==
                            0);
                        sock.reset();
                        MONAD_ASSERT(
                            task->io_submitted +
                                task->io_completed_not_reaped ==
                            0);
                        return monad_c_make_success(0);
                    }
                    process_completion(completed);
                }
                if (done) {
                    std::cout << time(nullptr) << ": Task " << task
                              << " begins processing completions for its "
                                 "connection port "
                              << ((sockaddr_in *)&sock->addr)->sin_port
                              << " having seen " << completions_processed
                              << " completions already processed." << std::endl;
                }
                for (;;) {
                    auto n = empty_completions_cancelling();
                    if (n == 0) {
                        break;
                    }
                    if (n < 0) {
                        if (done) {
                            std::cout << time(nullptr) << ": Task " << task
                                      << " receives cancellation request. "
                                         "io_submitted="
                                      << task->io_submitted
                                      << " io_completed_not_reaped="
                                      << task->io_completed_not_reaped
                                      << std::endl;
                        }
                        for (auto &i : iostatuses) {
                            auto r = to_result(
                                monad_async_task_io_cancel(task, &i.first));
                        }
                        if (done) {
                            std::cout << time(nullptr) << ": Task " << task
                                      << " has cancelled all i/o, begins "
                                         "processing completions. io_submitted="
                                      << task->io_submitted
                                      << " io_completed_not_reaped="
                                      << task->io_completed_not_reaped
                                      << std::endl;
                        }
                        while (empty_completions_non_cancelling())
                            ;
                        break;
                    }
                }
                try {
                    if (done) {
                        std::cout << time(nullptr) << ": Task " << task
                                  << " has emptied remaining i/o and now "
                                     "begins shutting down socket."
                                  << std::endl;
                    }
                    shutdown_socket();
                }
                catch (
                    const BOOST_OUTCOME_V2_NAMESPACE::experimental::
                        status_error<BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                         posix_code::domain_type> &e) {
                    std::cout << "NOTE: C++ exception thrown during socket "
                                 "shutdown in task "
                              << task << ": " << e.what() << std::endl;
                    while (empty_completions_non_cancelling())
                        ;
                    sock.reset();
                    return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                        monad, e.code());
                }
                if (done) {
                    std::cout << time(nullptr) << ": Task " << task
                              << " completes emptying remaining i/o and exits."
                              << std::endl;
                }
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
                sock.reset();
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
                return monad_c_make_success(0);
            }
            catch (const BOOST_OUTCOME_V2_NAMESPACE::experimental::status_error<
                   BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code::
                       domain_type> &e) {
                // std::cout << "NOTE: C++ exception thrown in task " << task
                //           << ": " << e.what() << std::endl;
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
                return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, e.code());
            }
            catch (...) {
                abort();
            }
        },
        [](monad_async_task task, bool const &done, int &) -> monad_c_result {
            try {
                if (done) {
                    std::cout << time(nullptr) << ": Setup task " << task
                              << " begins setting up a server socket."
                              << std::endl;
                }
                // Open a listening socket
                auto listening = make_socket(
                    task, AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0, 0);

                struct sockaddr_in localhost = {
                    .sin_family = AF_INET,
                    .sin_port = 0 /* any */,
                    .sin_addr = {.s_addr = htonl(INADDR_LOOPBACK)},
                    .sin_zero = {}};

                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(monad_async_task_socket_bind(
                    listening.get(),
                    (sockaddr *)&localhost,
                    sizeof(localhost)));
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    monad_async_task_socket_listen(listening.get(), 0));
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    monad_async_task_socket_transfer_to_uring(
                        task, listening.get()));
                // Copy out details of the bound socket for others to connect to
                memcpy(&server_socket, &listening->addr, sizeof(server_socket));
                struct server_task_t
                {
                    socket_ptr sock;
                    task_ptr task;
                };
                // There will be one of these subtasks running per server
                // connection
                auto server_subtask =
                    +[](monad_context_task task_) -> monad_c_result {
                    auto *task = (monad_async_task)task_;
                    auto *state = (server_task_t *)task->derived.user_ptr;
                    // std::cout << time(nullptr) << ": Setup subtask " << task
                    //           << " begins sending bytes to new connection
                    //           port "
                    //           << ((sockaddr_in
                    //           *)&state->sock->addr)->sin_port
                    //           << "." << std::endl;
                    monad_async_io_status status[3];
                    monad_async_task_registered_io_buffer buffer_rd{};
                    {
                        std::array<std::byte, 1024> buffer;
                        memset(buffer.data(), 0xea, 1024);
                        struct iovec iov[] = {{buffer.data(), 1024}};
                        struct msghdr msg = {};
                        msg.msg_iov = iov;
                        msg.msg_iovlen = 1;
                        // Begin a read to detect socket close
                        monad_async_task_socket_receive(
                            &status[0],
                            task,
                            state->sock.get(),
                            &buffer_rd,
                            1,
                            0);
                        // Send 1024 bytes to our new connection
                        monad_async_task_socket_send(
                            &status[1], task, state->sock.get(), 0, &msg, 0);
                        // Pump completions
                        while (monad_async_io_in_progress(status, 2) > 0) {
                            monad_async_io_status *completed;
                            auto r = to_result(
                                monad_async_task_suspend_until_completed_io(
                                    &completed,
                                    task,
                                    monad_async_duration_infinite_cancelling));
                            if (!r) {
                                if (monad_async_is_io_in_progress(&status[0])) {
                                    auto r =
                                        to_result(monad_async_task_io_cancel(
                                            task, &status[0]));
                                }
                                if (monad_async_is_io_in_progress(&status[1])) {
                                    auto r =
                                        to_result(monad_async_task_io_cancel(
                                            task, &status[1]));
                                }
                                break;
                            }
                        }
                    }
                    // std::cout << time(nullptr) << ": Setup subtask " << task
                    //           << " detects connection has closed. Beginning "
                    //              "shutdown ...."
                    //           << std::endl;
                    monad_async_task_socket_shutdown(
                        &status[2], task, state->sock.get(), SHUT_RDWR);
                    for (;;) {
                        monad_async_io_status *completed = nullptr;
                        auto r = to_result(
                            monad_async_task_suspend_until_completed_io(
                                &completed,
                                task,
                                monad_async_duration_infinite_non_cancelling));
                        if (r.value() == 0) {
                            break;
                        }
                    }
                    // std::cout << time(nullptr) << ": Setup subtask " << task
                    //           << " has completed connection shutdown,
                    //           exiting."
                    //           << std::endl;
                    MONAD_ASSERT(
                        task->io_submitted + task->io_completed_not_reaped ==
                        0);
                    state->sock.reset();
                    MONAD_ASSERT(
                        task->io_submitted + task->io_completed_not_reaped ==
                        0);
                    return monad_c_make_success(0);
                };
                std::list<server_task_t> server_tasks;
                while (!done) {
                    // Wait for an incoming connection
                    monad_async_socket sock;
                    // std::cout << time(nullptr) << ": Setup task " << task
                    //           << " waits for a new connection." << std::endl;
                    auto r = to_result(monad_async_task_socket_accept(
                        &sock, task, listening.get(), 0));
                    if (!r) {
                        if (r.assume_error() == errc::operation_canceled) {
                            break;
                        }
                        r.value();
                    }
                    // std::cout << time(nullptr) << ": Setup task " << task
                    //           << " accepts a new connection port "
                    //           << ((sockaddr_in *)&sock->addr)->sin_port <<
                    //           "."
                    //           << std::endl;
                    server_tasks.emplace_back(socket_ptr(
                        sock,
                        socket_deleter(task->current_executor.load(
                            std::memory_order_acquire))));
                    monad_async_task_attr task_attr{};
                    server_tasks.back().task = make_task(
                        task->derived.context->switcher.load(
                            std::memory_order_acquire),
                        task_attr);
                    server_tasks.back().task->derived.user_code =
                        server_subtask;
                    server_tasks.back().task->derived.user_ptr =
                        &server_tasks.back();
                    to_result(monad_async_task_attach(
                                  task->current_executor.load(
                                      std::memory_order_acquire),
                                  server_tasks.back().task.get(),
                                  nullptr))
                        .value();
                    while (!server_tasks.empty() &&
                           monad_async_task_has_exited(
                               server_tasks.front().task.get())) {
                        server_tasks.pop_front();
                    }
                }
                if (done) {
                    std::cout << time(nullptr) << ": Setup task " << task
                              << " closes the server socket." << std::endl;
                }
                listening.reset();
                std::erase_if(server_tasks, [](auto const &i) {
                    return monad_async_task_has_exited(i.task.get());
                });
                for (auto &i : server_tasks) {
                    auto r = to_result(monad_async_task_cancel(
                        task->current_executor.load(std::memory_order_acquire),
                        i.task.get()));
                }
                // Reduce my priority so suspend for duration doesn't become an
                // infinite loop
                to_result(monad_async_task_set_priorities(
                              task,
                              monad_async_priority_normal,
                              monad_async_priority_unchanged))
                    .value();
                if (done) {
                    std::cout << time(nullptr) << ": Setup task " << task
                              << " begins waiting for " << server_tasks.size()
                              << " server subtasks to exit." << std::endl;
                }
                while (!server_tasks.empty()) {
                    auto r = to_result(monad_async_task_suspend_for_duration(
                        nullptr, task, 100000000));
                    std::erase_if(server_tasks, [](auto const &i) {
                        return monad_async_task_has_exited(i.task.get());
                    });
                }
                if (done) {
                    std::cout << time(nullptr) << ": Setup task " << task
                              << " exits." << std::endl;
                }
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
                return monad_c_make_success(0);
            }
            catch (const BOOST_OUTCOME_V2_NAMESPACE::experimental::status_error<
                   BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code::
                       domain_type> &e) {
                MONAD_ASSERT(
                    task->io_submitted + task->io_completed_not_reaped == 0);
                return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, e.code());
            }
            catch (...) {
                abort();
            }
        });
}
