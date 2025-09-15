#pragma once

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/fiber/priority_task.hpp>
#include <category/core/likely.h>

#include <blockingconcurrentqueue.h>

#include <algorithm>
#include <cstdio>
#include <stop_token>
#include <thread>
#include <vector>

#include <pthread.h>
#include <sched.h>

MONAD_NAMESPACE_BEGIN

static_assert(std::is_same_v<std::jthread::native_handle_type, pthread_t>);

class ThreadPool
{
    unsigned const nthreads_;

    cpu_set_t const cpu_set_;

    moodycamel::BlockingConcurrentQueue<fiber::PriorityTask> queue_{};

    std::vector<std::jthread> threads_{};

    std::vector<int64_t> requested_{};

    std::vector<unsigned> sorted_{};

    std::jthread priority_thread_{};

    void update_priorities()
    {
        /**
         * TODO this code should sort, group by number of cores (from cpu_set),
         * then try to find the minimum number of adjustments to get the desired
         * ordering
         *
         * the below code is just a lazy way to get it working for the moment
         */
        std::sort(
            sorted_.begin(),
            sorted_.end(),
            [this](unsigned const i, unsigned const j) {
                return requested_[i] < requested_[j];
            });
        int priority = 99;
        for (auto &thread : threads_) {
            MONAD_ASSERT(
                !pthread_setschedprio(thread.native_handle(), priority--));
        }
    }

public:
    ThreadPool(unsigned const nthreads, cpu_set_t const cpu_set)
        : nthreads_{nthreads}
        , cpu_set_{cpu_set}
        , requested_(nthreads_, INT64_MAX)
    {
        threads_.reserve(nthreads_);
        for (unsigned i = 0; i < nthreads_; ++i) {
            std::jthread thread{[this, i](std::stop_token const stop_token) {
                {
                    char name[16];
                    std::snprintf(name, 16, "worker %u", i);
                    pthread_setname_np(pthread_self(), name);
                }

                MONAD_ASSERT(!pthread_setaffinity_np(
                    pthread_self(), sizeof(cpu_set_), &cpu_set_));

                {
                    sched_param sched{};
                    sched.sched_priority = 1;
                    MONAD_ASSERT(!pthread_setschedparam(
                        pthread_self(), SCHED_FIFO, &sched));
                }

                while (!stop_token.stop_requested()) {
                    fiber::PriorityTask task{};
                    if (MONAD_LIKELY(queue_.wait_dequeue_timed(task, 100000))) {
                        requested_[i] = task.priority;
                        task.task();
                        requested_[i] = INT64_MAX;
                        MONAD_ASSERT(!pthread_setschedprio(pthread_self(), 1));
                    }
                }
            }};
            threads_.emplace_back(std::move(thread));
            sorted_.emplace_back(i);
        }

        std::jthread priority_thread{[this](std::stop_token const stop_token) {
            while (!stop_token.stop_requested()) {
                update_priorities();
                std::this_thread::sleep_for(std::chrono::microseconds{50});
            }
        }};
        priority_thread_ = std::move(priority_thread);
    }

    ~ThreadPool()
    {
        priority_thread_.request_stop();
        priority_thread_.join();

        for (auto &thread : threads_) {
            thread.request_stop();
        }
        while (!threads_.empty()) {
            auto &thread = threads_.back();
            thread.join();
            threads_.pop_back();
        }
    }

    void submit(uint64_t const priority, std::function<void()> task)
    {
        MONAD_ASSERT(queue_.enqueue({priority, std::move(task)}));
    }
};

MONAD_NAMESPACE_END
