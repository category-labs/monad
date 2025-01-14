#include <gtest/gtest.h>

#include "../../test_common.hpp"

#include <monad/async/cpp_helpers.hpp>
#include <monad/async/executor.h>
#include <monad/async/task.h>
#include <monad/context/config.h>
#include <monad/context/context_switcher.h>
#include <monad/util/temp_files.h>

#include <monad/core/assert.h>
#include <monad/core/scope_polyfill.hpp>
#include <monad/core/small_prng.hpp>

#include <boost/outcome/config.hpp>
#include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#include <boost/outcome/experimental/status-code/status-code/status_error.hpp>

#include <chrono>
#include <type_traits>

#include <netinet/in.h>

template <class F>
    requires(std::is_invocable_r_v<
             monad_c_result, F, monad_async_task, bool const &>)
static void test_cancellation(char const *desc, F &&op)
{
    {
        monad_async_executor_attr ex_attr{};
        ex_attr.io_uring_ring.entries = 16;
        ex_attr.io_uring_ring.registered_buffers.small_count = 64 + 4;
        ex_attr.io_uring_wr_ring.entries = 16;
        auto ex = make_executor(ex_attr);
        auto switcher = make_context_switcher(monad_context_switcher_fcontext);

        struct shared_t
        {
            F &op;
            bool done{false};
            uint32_t ops{0};
        } shared{op};

        auto task_impl = +[](monad_context_task task_) -> monad_c_result {
            auto *task = (monad_async_task)task_;
            auto *shared = (shared_t *)task->derived.user_ptr;
            while (!shared->done) {
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(
                    shared->op(task, shared->done));
                shared->ops++;
            }
            MONAD_ASSERT(task->io_submitted == 0);
            MONAD_ASSERT(task->io_completed_not_reaped == 0);
            return monad_c_make_success(0);
        };

        std::vector<task_ptr> tasks;
        tasks.reserve(ex_attr.io_uring_ring.entries + 8);
        monad_async_task_attr task_attr{};
        for (size_t n = 0; n < tasks.capacity(); n++) {
            tasks.push_back(make_task(switcher.get(), task_attr));
            tasks.back()->derived.user_code = task_impl;
            tasks.back()->derived.user_ptr = &shared;
            to_result(
                monad_async_task_attach(ex.get(), tasks.back().get(), nullptr))
                .value();
        }

        monad::small_prng rand;

        const struct timespec nowait = {};

        std::cout << "Beginning testing " << desc
                  << " for correctness in cancellation for three seconds ..."
                  << std::endl;
        uint32_t implicit_cancels = 0, explicit_cancels = 0;
        auto const begin = std::chrono::steady_clock::now();
        do {
            auto const v = rand();
            task_ptr &i = tasks[v % tasks.size()];
            assert(i);
            if ((v >> 29) == 0) {
                // Implicit cancellation
                i.reset();
                implicit_cancels++;
            }
            else {
                // Explicit cancellation
                auto r = to_result(monad_async_task_cancel(ex.get(), i.get()));
                if (!r) {
                    if (r.assume_error() !=
                        errc::resource_unavailable_try_again) {
                        r.value();
                    }
                }
                while (!monad_async_task_has_exited(i.get())) {
                    auto r = to_result(monad_async_executor_run(
                        ex.get(), size_t(-1), &nowait));
                    if (!r && r.assume_error() != errc::stream_timeout) {
                        r.value();
                    }
                }
                explicit_cancels++;
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
        std::cout << "\nStopping initiating new i/o and cancellations (i/o "
                     "buffer deadlocks = "
                  << ex->registered_buffers.total_deadlocks_broken << ") ..."
                  << std::endl;
        shared.done = true;
        struct timespec ts = {.tv_sec = 10, .tv_nsec = 0};
        while (monad_async_executor_has_work(ex.get())) {
            auto r =
                to_result(monad_async_executor_run(ex.get(), size_t(-1), &ts));
            if (!r) {
                auto const *desc =
                    (char const *)to_result(
                        monad_async_executor_debug_string(ex.get()))
                        .value();
                std::cout << "\nRunning executor after requesting quit has "
                             "failed. Internal debug for the executor is:\n"
                          << desc << std::endl;
                free((void *)desc);
                r.value();
            }
        }
        EXPECT_GT(shared.ops, 0);
        EXPECT_GT(implicit_cancels, 0);
        EXPECT_GT(explicit_cancels, 0);
        std::cout << "Testing of " << desc
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
    }
    std::cout << "Testing of " << desc
              << " for correctness in cancellation has torn down everything "
                 "successfully."
              << std::endl;
}

TEST(cancellation, yield)
{
    test_cancellation(
        "yield", [](monad_async_task task, bool const &) -> monad_c_result {
            return monad_async_task_suspend_for_duration(nullptr, task, 0);
        });
}

TEST(cancellation, suspend_for_duration)
{
    test_cancellation(
        "suspend for duration",
        [](monad_async_task task, bool const &) -> monad_c_result {
            return monad_async_task_suspend_for_duration(
                nullptr, task, 1000000ULL); // 1 millisecond
        });
}

TEST(cancellation, file_open_close)
{
    test_cancellation(
        "file open close",
        [](monad_async_task task, bool const &) -> monad_c_result {
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
    test_cancellation(
        "socket open close",
        [](monad_async_task task, bool const &) -> monad_c_result {
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
    test_cancellation(
        "file read",
        [](monad_async_task task, bool const &done) -> monad_c_result {
            std::array<
                std::pair<
                    monad_async_io_status,
                    monad_async_task_registered_io_buffer>,
                1000>
                iostatuses;
            auto uniostatuses = monad::make_scope_exit([&]() noexcept {
                for (auto &i : iostatuses) {
                    MONAD_ASSERT(i.second.index == 0);
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
                    CHECK_RESULT(monad_async_task_suspend_until_completed_io(
                        &completed,
                        task,
                        monad_async_duration_infinite_non_cancelling));
                    if (completed == nullptr) {
                        break;
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
                        std::cout << "Task " << task << " initiates i/o "
                                  << &iostatuses[n].first << " (" << n << "/"
                                  << iostatuses.size() << ")" << std::endl;
                    }
                    memset(
                        &iostatuses[n].second, 0, sizeof(iostatuses[n].second));
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
                    std::cout << "Task " << task
                              << " stops initiating new i/o and starts "
                                 "emptying remaining i/o."
                              << std::endl;
                }
                empty_completions();
                if (done) {
                    std::cout << "Task " << task
                              << " completes emptying remaining i/o and exits."
                              << std::endl;
                }
                fh.reset();
                return monad_c_make_success(0);
            }
            catch (const BOOST_OUTCOME_V2_NAMESPACE::experimental::status_error<
                   BOOST_OUTCOME_V2_NAMESPACE::experimental::posix_code::
                       domain_type> &e) {
                empty_completions();
                return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(monad, e.code());
            }
            catch (...) {
                abort();
            }
        });
}

// This code will be used in further tests yet to be written
#if 0
        CHECK_RESULT(monad_async_task_suspend_for_duration(
            nullptr,
            ((monad_async_task)task),
            10000000ULL)); // 10 milliseconds
        EXPECT_EQ(ex->total_io_submitted, 1);
        EXPECT_EQ(ex->total_io_completed, 1);
        for (size_t n = 0; n < 100; n++) {
            CHECK_RESULT(monad_async_task_suspend_for_duration(
                nullptr,
                ((monad_async_task)task),
                1000000ULL)); // 1 milliseconds
        }
        EXPECT_EQ(ex->total_io_submitted, 101);
        EXPECT_EQ(ex->total_io_completed, 101);

        struct open_how how
        {
            .flags = O_RDWR, .mode = 0, .resolve = 0
        };

        char tempfilepath[256];
        close(monad_make_temporary_file(
            tempfilepath, sizeof(tempfilepath)));
        auto fh = make_file(task, nullptr, tempfilepath, how);
        unlink(tempfilepath);
        EXPECT_EQ(ex->total_io_submitted, 103);
        EXPECT_EQ(ex->total_io_completed, 103);
        CHECK_RESULT(
            monad_async_task_file_fallocate(task, fh.get(), 0, 0, 1024));
        EXPECT_EQ(ex->total_io_submitted, 104);
        EXPECT_EQ(ex->total_io_completed, 104);

        std::array<
            std::pair<
                monad_async_io_status,
                monad_async_task_registered_io_buffer>,
            1000>
            iostatuses;
        auto process_completion = [&](monad_async_io_status *completed) {
            if (completed == nullptr) {
                return;
            }
            EXPECT_TRUE(to_result(completed->result).has_value());
            auto *i = (std::pair<
                       monad_async_io_status,
                       monad_async_task_registered_io_buffer> *)completed;
            CHECK_RESULT(monad_async_task_release_registered_io_buffer(
                task, i->second.index));
        };
        for (size_t n = 0; n < iostatuses.size(); n++) {
            monad_async_task_file_read(
                &iostatuses[n].first,
                task,
                fh.get(),
                &iostatuses[n].second,
                1,
                n,
                0);
            process_completion(monad_async_task_completed_io(task));
        }
        EXPECT_EQ(ex->total_io_submitted, 1104);
        EXPECT_LE(ex->total_io_completed, 1104);
        for (;;) {
            monad_async_io_status *completed = nullptr;
            CHECK_RESULT(monad_async_task_suspend_until_completed_io(
                &completed,
                task,
                monad_async_duration_infinite_non_cancelling));
            if (completed == nullptr) {
                break;
            }
            process_completion(completed);
        }
        EXPECT_EQ(ex->total_io_submitted, 1104);
        EXPECT_EQ(ex->total_io_completed, 1104);

        return monad_c_make_success(0);
    };
    CHECK_RESULT(monad_async_task_attach(ex.get(), task.get(), nullptr));
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
#endif
