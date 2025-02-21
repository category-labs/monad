#include <gtest/gtest.h>

#include "../../test_common.hpp"

#include <monad/context/config.h>

#include "../cpp_helpers.hpp"
#include "../executor.h"
#include "../file_io.h"
#include "../task.h"
#include "../util.h"

#include <array>
#include <atomic>
#include <chrono>
#include <memory>
#include <vector>

#include <fcntl.h>
#include <unistd.h>

TEST(file_io, unregistered_buffers)
{
    struct shared_state_t
    {
        char tempfilepath[256];

        shared_state_t()
        {
            int const fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
            close(fd);
        }

        ~shared_state_t()
        {
            unlink(tempfilepath);
        }

        monad_c_result task(monad_async_task task)
        {
            // Open the file
            struct open_how how
            {
                .flags = O_RDWR, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            EXPECT_EQ(fh->executor, task->current_executor);
            std::cout << "   Opening the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Write to the file
            {
                monad_async_io_status iostatus{};
                struct iovec const iov[] = {
                    {.iov_base = (void *)"hello world", .iov_len = 11}};
                EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
                monad_async_task_file_write(
                    &iostatus, task, fh.get(), 0, &iov[0], 1, 0, 0);
                EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
                EXPECT_EQ(task->io_submitted, 1);
                EXPECT_EQ(task->io_completed_not_reaped, 0);
                monad_async_io_status *completed = nullptr;
                EXPECT_EQ(
                    to_result(monad_async_task_suspend_until_completed_io(
                                  &completed, task, (uint64_t)-1))
                        .value(),
                    1);
                EXPECT_EQ(task->io_submitted, 0);
                EXPECT_EQ(task->io_completed_not_reaped, 0);
                EXPECT_EQ(completed, &iostatus);
                EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
                to_result(iostatus.result).value();
                std::cout << "   The write took "
                          << (iostatus.ticks_when_completed -
                              iostatus.ticks_when_initiated)
                          << " ticks." << std::endl;
            }

            char buffer[64]{};
            // Initiate two concurrent reads
            monad_async_io_status iostatus[2]{};
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[0]));
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[1]));
            struct iovec const iov[] = {
                {.iov_base = buffer, .iov_len = 6},
                {.iov_base = buffer + 6, .iov_len = 6}};
            monad_async_task_file_readv(
                &iostatus[0], task, fh.get(), &iov[0], 1, 0, 0);
            monad_async_task_file_readv(
                &iostatus[1], task, fh.get(), &iov[1], 1, 6, 0);
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus[0]));
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus[1]));
            EXPECT_EQ(task->io_submitted, 2);
            EXPECT_EQ(task->io_completed_not_reaped, 0);

            // Wait until both reads have completed
            while (monad_async_io_in_progress(iostatus, 2) > 0) {
                monad_async_io_status *completed = nullptr;
                to_result(monad_async_task_suspend_for_duration(
                              &completed, task, (uint64_t)-1))
                    .value();
                EXPECT_TRUE(
                    completed == &iostatus[0] || completed == &iostatus[1]);
            }
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 2);

            // Iterate through all completed i/o for this task
            for (auto *completed = monad_async_task_completed_io(task);
                 completed != nullptr;
                 completed = monad_async_task_completed_io(task)) {
                EXPECT_TRUE(to_result(completed->result).has_value());
            }
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);

            EXPECT_STREQ(buffer, "hello world");
            EXPECT_EQ(to_result(iostatus[0].result).value(), 6);
            EXPECT_EQ(to_result(iostatus[1].result).value(), 5);
            std::cout << "   The first read took "
                      << (iostatus[0].ticks_when_completed -
                          iostatus[0].ticks_when_initiated)
                      << " ticks." << std::endl;
            std::cout << "   The second read took "
                      << (iostatus[1].ticks_when_completed -
                          iostatus[1].ticks_when_initiated)
                      << " ticks." << std::endl;

            fh.reset();
            std::cout << "   Closing the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;
            return monad_c_make_success(0);
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    ex_attr.io_uring_wr_ring.entries = 8;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and a task, and attach the task to the executor
    auto s = make_context_switcher(monad_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t = make_task(s.get(), t_attr);
    t->derived.user_ptr = (void *)&shared_state;
    t->derived.user_code = +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)->task((monad_async_task)task);
    };
    to_result(monad_async_task_attach(ex.get(), t.get(), nullptr)).value();

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
}

TEST(file_io, registered_buffers)
{
    struct shared_state_t
    {
        char tempfilepath[256];

        shared_state_t()
        {
            int const fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
            close(fd);
        }

        ~shared_state_t()
        {
            unlink(tempfilepath);
        }

        monad_c_result task(monad_async_task task)
        {
            // Open the file
            struct open_how how
            {
                .flags = O_RDWR, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            EXPECT_EQ(fh->executor, task->current_executor);
            std::cout << "   Opening the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Write to the file
            {
                monad_async_task_registered_io_buffer buffer;
                to_result(
                    monad_async_task_claim_registered_file_io_write_buffer(
                        &buffer, task, 4097, {}))
                    .value();
                monad_async_io_status iostatus{};
                memcpy(buffer.iov->iov_base, "hello world", 11);
                EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
                struct iovec const iov[] = {
                    {.iov_base = buffer.iov[0].iov_base, .iov_len = 11}};
                monad_async_task_file_write(
                    &iostatus, task, fh.get(), buffer.index, &iov[0], 1, 0, 0);
                EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
                EXPECT_EQ(task->io_submitted, 1);
                EXPECT_EQ(task->io_completed_not_reaped, 0);
                monad_async_io_status *completed = nullptr;
                EXPECT_EQ(
                    to_result(monad_async_task_suspend_until_completed_io(
                                  &completed, task, (uint64_t)-1))
                        .value(),
                    1);
                EXPECT_EQ(task->io_submitted, 0);
                EXPECT_EQ(task->io_completed_not_reaped, 0);
                EXPECT_EQ(completed, &iostatus);
                EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
                to_result(iostatus.result).value();
                std::cout << "   The write took "
                          << (iostatus.ticks_when_completed -
                              iostatus.ticks_when_initiated)
                          << " ticks." << std::endl;
                to_result(monad_async_task_release_registered_io_buffer(
                              task, buffer.index))
                    .value();
            }

            // Get my registered buffer
            // Initiate two concurrent reads
            monad_async_io_status iostatus[2]{};
            monad_async_task_registered_io_buffer buffer[2]{};
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[0]));
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus[1]));
            monad_async_task_file_read(
                &iostatus[0], task, fh.get(), &buffer[0], 6, 0, 0);
            monad_async_task_file_read(
                &iostatus[1], task, fh.get(), &buffer[1], 6, 6, 0);
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus[0]));
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus[1]));
            EXPECT_EQ(task->io_submitted, 2);
            EXPECT_EQ(task->io_completed_not_reaped, 0);

            // Wait until both reads have completed
            while (monad_async_io_in_progress(iostatus, 2) > 0) {
                monad_async_io_status *completed = nullptr;
                to_result(monad_async_task_suspend_for_duration(
                              &completed, task, (uint64_t)-1))
                    .value();
                EXPECT_TRUE(
                    completed == &iostatus[0] || completed == &iostatus[1]);
            }
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 2);

            // Iterate through all completed i/o for this task
            for (auto *completed = monad_async_task_completed_io(task);
                 completed != nullptr;
                 completed = monad_async_task_completed_io(task)) {
                auto r = to_result(completed->result);
                EXPECT_TRUE(r.has_value());
                r.value();
            }
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);

            ((char *)buffer[0].iov[0].iov_base)[6] = 0;
            ((char *)buffer[1].iov[0].iov_base)[5] = 0;
            EXPECT_STREQ((char const *)buffer[0].iov[0].iov_base, "hello ");
            EXPECT_STREQ((char const *)buffer[1].iov[0].iov_base, "world");
            EXPECT_EQ(to_result(iostatus[0].result).value(), 6);
            EXPECT_EQ(to_result(iostatus[1].result).value(), 5);
            std::cout << "   The first read took "
                      << (iostatus[0].ticks_when_completed -
                          iostatus[0].ticks_when_initiated)
                      << " ticks." << std::endl;
            std::cout << "   The second read took "
                      << (iostatus[1].ticks_when_completed -
                          iostatus[1].ticks_when_initiated)
                      << " ticks." << std::endl;

            fh.reset();
            std::cout << "   Closing the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            to_result(monad_async_task_release_registered_io_buffer(
                          task, buffer[0].index))
                .value();
            to_result(monad_async_task_release_registered_io_buffer(
                          task, buffer[1].index))
                .value();
            return monad_c_make_success(0);
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 64;
    ex_attr.io_uring_ring.registered_buffers.small_count = 2;
    ex_attr.io_uring_wr_ring.entries = 8;
    ex_attr.io_uring_wr_ring.registered_buffers.large_count = 1;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and a task, and attach the task to the executor
    auto s = make_context_switcher(monad_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t = make_task(s.get(), t_attr);
    t->derived.user_ptr = (void *)&shared_state;
    t->derived.user_code = +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)->task((monad_async_task)task);
    };
    to_result(monad_async_task_attach(ex.get(), t.get(), nullptr)).value();

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
}

TEST(file_io, misc_ops)
{
    struct shared_state_t
    {
        char tempfilepath[256];

        shared_state_t()
        {
            int const fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
            close(fd);
        }

        ~shared_state_t()
        {
            unlink(tempfilepath);
        }

        monad_c_result task(monad_async_task task)
        {
            // Open the file
            struct open_how how
            {
                .flags = O_RDWR, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            EXPECT_EQ(fh->executor, task->current_executor);
            std::cout << "   Opening the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Preallocate the contents
            to_result(monad_async_task_file_fallocate(
                          task, fh.get(), FALLOC_FL_ZERO_RANGE, 0, 11))
                .value();
            std::cout << "   Preallocating the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;

            // Write to the file
            monad_async_io_status iostatus{};
            struct iovec const iov[] = {
                {.iov_base = (void *)"hello world", .iov_len = 11}};
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            monad_async_task_file_write(
                &iostatus, task, fh.get(), 0, &iov[0], 1, 0, 0);
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
            EXPECT_EQ(task->io_submitted, 1);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            monad_async_io_status *completed = nullptr;
            EXPECT_EQ(
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value(),
                1);
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            EXPECT_EQ(completed, &iostatus);
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            to_result(iostatus.result).value();
            std::cout << "   The write took "
                      << (iostatus.ticks_when_completed -
                          iostatus.ticks_when_initiated)
                      << " ticks." << std::endl;

            // Initialise sync to disc for the range without waiting for it to
            // reach the disc
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            monad_async_task_file_range_sync(
                &iostatus,
                task,
                fh.get(),
                0,
                11,
                SYNC_FILE_RANGE_WAIT_BEFORE | SYNC_FILE_RANGE_WRITE);
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
            EXPECT_EQ(task->io_submitted, 1);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            completed = nullptr;
            EXPECT_EQ(
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value(),
                1);
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            EXPECT_EQ(completed, &iostatus);
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            to_result(iostatus.result).value();
            std::cout << "   The write barrier took "
                      << (iostatus.ticks_when_completed -
                          iostatus.ticks_when_initiated)
                      << " ticks." << std::endl;

            // Synchronise the writes to the file fully with storage in a sudden
            // power loss retrievable way
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            monad_async_task_file_durable_sync(&iostatus, task, fh.get());
            EXPECT_TRUE(monad_async_is_io_in_progress(&iostatus));
            EXPECT_EQ(task->io_submitted, 1);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            completed = nullptr;
            EXPECT_EQ(
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value(),
                1);
            EXPECT_EQ(task->io_submitted, 0);
            EXPECT_EQ(task->io_completed_not_reaped, 0);
            EXPECT_EQ(completed, &iostatus);
            EXPECT_FALSE(monad_async_is_io_in_progress(&iostatus));
            to_result(iostatus.result).value();
            std::cout << "   The durable sync took "
                      << (iostatus.ticks_when_completed -
                          iostatus.ticks_when_initiated)
                      << " ticks." << std::endl;

            fh.reset();
            std::cout << "   Closing the file took "
                      << (task->ticks_when_suspended_completed -
                          task->ticks_when_suspended_awaiting)
                      << " ticks." << std::endl;
            return monad_c_make_success(0);
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 8;
    ex_attr.io_uring_wr_ring.entries = 8;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and a task, and attach the task to the executor
    auto s = make_context_switcher(monad_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t = make_task(s.get(), t_attr);
    t->derived.user_ptr = (void *)&shared_state;
    t->derived.user_code = +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)->task((monad_async_task)task);
    };
    to_result(monad_async_task_attach(ex.get(), t.get(), nullptr)).value();

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
}

TEST(file_io, benchmark)
{
    struct shared_state_t
    {
        char tempfilepath[256];
        bool done{false};

        shared_state_t()
        {
            int const fd = monad_async_make_temporary_file(
                tempfilepath, sizeof(tempfilepath));
            static constexpr std::string_view text(
                R"(Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.
      Sed ut perspiciatis unde omnis iste natus error sit voluptatem accusantium doloremque laudantium, totam rem aperiam, eaque ipsa quae ab illo inventore veritatis et quasi architecto beatae vitae dicta sunt explicabo. Nemo enim ipsam voluptatem quia voluptas sit aspernatur aut odit aut fugit, sed quia consequuntur magni dolores eos qui ratione voluptatem sequi nesciunt. Neque porro quisquam est, qui dolorem ipsum quia dolor sit amet, consectetur, adipisci velit, sed quia non numquam eius modi tempora incidunt ut labore et dolore magnam aliquam quaerat voluptatem. Ut enim ad minima veniam, quis nostrum exercitationem ullam corporis suscipit laboriosam, nisi ut aliquid ex ea commodi consequatur? Quis autem vel eum iure reprehenderit qui in ea voluptate velit esse quam nihil molestiae consequatur, vel illum qui dolorem eum fugiat quo voluptas nulla pariatur?
)");
            for (size_t length = 0; length < 64 * 512; length += text.size()) {
                if (-1 == write(fd, text.data(), text.size())) {
                    abort();
                }
            }
            close(fd);
        }

        ~shared_state_t()
        {
            unlink(tempfilepath);
        }

        monad_c_result
        task(monad_async_task task, monad_async_priority priority)
        {
            std::cout << "Task " << task << " begins with priority "
                      << (int)priority << std::endl;
            to_result(monad_async_task_set_priorities(
                          task, priority, monad_async_priority_unchanged))
                .value();

            // Open the file
            struct open_how how
            {
                .flags = O_RDONLY | O_DIRECT, .mode = 0, .resolve = 0
            };

            auto fh = make_file(task, nullptr, tempfilepath, how);
            std::vector<std::pair<
                monad_async_io_status,
                monad_async_task_registered_io_buffer>>
                iostatus(
                    128,
                    {monad_async_io_status{},
                     monad_async_task_registered_io_buffer{}});
            uint32_t ops = 0;

            auto const begin = std::chrono::steady_clock::now();
            for (size_t n = 0; n < iostatus.size(); n++) {
                monad_async_task_file_read(
                    &iostatus[n].first,
                    task,
                    fh.get(),
                    &iostatus[n].second,
                    512,
                    n * 512,
                    0);
                ops++;
            }
            while (!done) {
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed, task, (uint64_t)-1))
                    .value();
                auto idx =
                    size_t((uintptr_t)completed - (uintptr_t)iostatus.data()) /
                    sizeof(std::pair<
                           monad_async_io_status,
                           monad_async_task_registered_io_buffer>);
                assert(&iostatus[idx].first == completed);
                to_result(monad_async_task_release_registered_io_buffer(
                              task, iostatus[idx].second.index))
                    .value();
                iostatus[idx].second.iov[0].iov_base = nullptr;
                monad_async_task_file_read(
                    completed,
                    task,
                    fh.get(),
                    &iostatus[idx].second,
                    512,
                    idx * 512,
                    0);
                ops++;
            }
            while (task->io_submitted + task->io_completed_not_reaped > 0) {
                monad_async_io_status *completed;
                if (to_result(monad_async_task_suspend_until_completed_io(
                                  &completed, task, 0))
                        .value() == 0) {
                    continue;
                }
                auto idx =
                    size_t((uintptr_t)completed - (uintptr_t)iostatus.data()) /
                    sizeof(std::pair<
                           monad_async_io_status,
                           monad_async_task_registered_io_buffer>);
                to_result(monad_async_task_release_registered_io_buffer(
                              task, iostatus[idx].second.index))
                    .value();
            }
            auto const end = std::chrono::steady_clock::now();
            auto const diff =
                double(std::chrono::duration_cast<std::chrono::nanoseconds>(
                           end - begin)
                           .count());
            std::cout << "   Task priority " << (int)priority << " did " << ops
                      << " read i/o which is "
                      << (1000000000.0 * (double)ops / diff)
                      << " ops/sec (which is " << (diff / (double)ops)
                      << " ns/op)" << std::endl;
            return monad_c_make_success(0);
        }
    } shared_state;

    // Make an executor
    monad_async_executor_attr ex_attr{};
    ex_attr.io_uring_ring.entries = 128;
    ex_attr.io_uring_ring.registered_buffers.small_count = 256;
    auto ex = make_executor(ex_attr);

    // Make a context switcher and two tasks which do the same thing, but with
    // different priority
    auto s = make_context_switcher(monad_context_switcher_sjlj);
    monad_async_task_attr t_attr{};
    auto t1 = make_task(s.get(), t_attr);
    t1->derived.user_ptr = (void *)&shared_state;
    t1->derived.user_code = +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)
            ->task((monad_async_task)task, monad_async_priority_normal);
    };
    auto t2 = make_task(s.get(), t_attr);
    t2->derived.user_ptr = (void *)&shared_state;
    t2->derived.user_code = +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)
            ->task((monad_async_task)task, monad_async_priority_high);
    };
    to_result(monad_async_task_attach(ex.get(), t1.get(), nullptr)).value();
    to_result(monad_async_task_attach(ex.get(), t2.get(), nullptr)).value();

    // Run the executor for five seconds
    auto const begin = std::chrono::steady_clock::now();
    for (;;) {
        to_result(monad_async_executor_run(ex.get(), 1024, nullptr)).value();
        if (std::chrono::steady_clock::now() - begin >=
            std::chrono::seconds(5)) {
            break;
        }
    }
    shared_state.done = true;

    // Run the executor until all tasks exit
    while (monad_async_executor_has_work(ex.get())) {
        to_result(monad_async_executor_run(ex.get(), size_t(-1), nullptr))
            .value();
    }
    EXPECT_EQ(ex->total_io_submitted, ex->total_io_completed);
}

TEST(file_io, sqe_exhaustion_does_not_reorder_writes)
{
    static constexpr size_t COUNT = 64;

    struct shared_state_t
    {
        executor_ptr ex;
        context_switcher_ptr switcher;
        uint32_t offset{0};
        std::vector<monad_async_file_offset> seq;
        std::vector<task_ptr> tasks;
        std::optional<file_ptr> fh;

        shared_state_t()
        {
            monad_async_executor_attr ex_attr{};
            ex_attr.io_uring_ring.entries = 4;
            ex_attr.io_uring_wr_ring.entries = 4;
            ex_attr.io_uring_wr_ring.registered_buffers.small_count = COUNT / 2;
            ex = make_executor(ex_attr);

            switcher = make_context_switcher(monad_context_switcher_sjlj);

            seq.reserve(COUNT * 4);
            tasks.reserve(COUNT * 4);
        }

        ~shared_state_t()
        {
            monad_async_task_attr t_attr{};
            auto t = make_task(switcher.get(), t_attr);
            t->derived.user_ptr = (void *)this;
            t->derived.user_code =
                +[](monad_context_task task) -> monad_c_result {
                auto *shared_state = (shared_state_t *)task->user_ptr;
                shared_state->fh.reset();
                return monad_c_make_success(0);
            };
            to_result(monad_async_task_attach(ex.get(), t.get(), nullptr))
                .value();
            do {
                to_result(
                    monad_async_executor_run(ex.get(), size_t(-1), nullptr))
                    .value();
            }
            while (monad_async_executor_has_work(ex.get()));
            assert(!fh.has_value());
        }

        monad_c_result task(monad_async_task task)
        {
            if (!fh) {
                monad_async_file file;
                int const fd = monad_async_make_temporary_inode();
                to_result(monad_async_task_file_create_from_existing_fd(
                              &file, task, fd))
                    .value();
                close(fd);
                fh = std::unique_ptr<monad_async_file_head, file_deleter>(
                    file,
                    file_deleter(task->current_executor.load(
                        std::memory_order_acquire)));
            }
            else {
                monad_async_task_registered_io_buffer buffer;
                to_result(
                    monad_async_task_claim_registered_file_io_write_buffer(
                        &buffer, task, 512, {}))
                    .value();
                auto myoffset = offset;
                offset += 512;
                monad_async_io_status status{};
                monad_async_task_file_write(
                    &status,
                    task,
                    fh->get(),
                    buffer.index,
                    buffer.iov,
                    1,
                    myoffset,
                    0);
                monad_async_io_status *completed;
                to_result(monad_async_task_suspend_until_completed_io(
                              &completed,
                              task,
                              monad_async_duration_infinite_non_cancelling))
                    .value();
                if (completed != &status) {
                    abort();
                }
                if (seq.size() == seq.capacity()) {
                    abort();
                }
                seq.push_back(myoffset);
                std::cout << seq.size() << std::endl;
                to_result(monad_async_task_release_registered_io_buffer(
                              task, buffer.index))
                    .value();
            }

            if (seq.size() < COUNT) {
                monad_async_task_attr t_attr{};
                tasks.emplace_back(make_task(switcher.get(), t_attr));
                tasks.back()->derived.user_ptr = (void *)this;
                tasks.back()->derived.user_code =
                    +[](monad_context_task task) -> monad_c_result {
                    return ((shared_state_t *)task->user_ptr)
                        ->task((monad_async_task)task);
                };
                to_result(monad_async_task_attach(
                              ex.get(), tasks.back().get(), nullptr))
                    .value();
                tasks.emplace_back(make_task(switcher.get(), t_attr));
                tasks.back()->derived.user_ptr = (void *)this;
                tasks.back()->derived.user_code =
                    +[](monad_context_task task) -> monad_c_result {
                    return ((shared_state_t *)task->user_ptr)
                        ->task((monad_async_task)task);
                };
                to_result(monad_async_task_attach(
                              ex.get(), tasks.back().get(), nullptr))
                    .value();
                tasks.emplace_back(make_task(switcher.get(), t_attr));
                tasks.back()->derived.user_ptr = (void *)this;
                tasks.back()->derived.user_code =
                    +[](monad_context_task task) -> monad_c_result {
                    return ((shared_state_t *)task->user_ptr)
                        ->task((monad_async_task)task);
                };
                to_result(monad_async_task_attach(
                              ex.get(), tasks.back().get(), nullptr))
                    .value();
            }
            return monad_c_make_success(0);
        }
    } shared_state;

    monad_async_task_attr t_attr{};
    auto t = make_task(shared_state.switcher.get(), t_attr);
    t->derived.user_ptr = (void *)&shared_state;
    t->derived.user_code = +[](monad_context_task task) -> monad_c_result {
        return ((shared_state_t *)task->user_ptr)->task((monad_async_task)task);
    };
    to_result(monad_async_task_attach(shared_state.ex.get(), t.get(), nullptr))
        .value();
    do {
        to_result(monad_async_executor_run(
                      shared_state.ex.get(), size_t(-1), nullptr))
            .value();
    }
    while (monad_async_executor_has_work(shared_state.ex.get()));
    EXPECT_EQ(
        shared_state.ex->total_io_submitted,
        shared_state.ex->total_io_completed);
    std::cout << "   " << shared_state.seq.size() << " offsets written."
              << std::endl;

    uint32_t offset2 = 0;
    for (auto &i : shared_state.seq) {
        EXPECT_EQ(i, offset2);
        offset2 += 512;
    }
    EXPECT_EQ(shared_state.seq.back(), shared_state.offset - 512);
}
