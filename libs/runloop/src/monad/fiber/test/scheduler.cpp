#include <gtest/gtest.h>

#include "monad/fiber/assert.h"
#include <algorithm>
#include <monad/fiber/scheduler.h>
#include <shared_mutex>
#include <thread>
#include <vector>

monad_fiber_scheduler sched;
std::atomic_size_t resumed;
int64_t priority = 0;

void wait(monad_fiber_scheduler_t &s)
{
    while (true) {
        MONAD_CCALL_ASSERT(pthread_mutex_lock(&s.mutex));
        auto sz = s.task_queue.size;
        MONAD_CCALL_ASSERT(pthread_mutex_unlock(&s.mutex));
        if (sz == 0u) {
            break;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(10));
    }
}

struct task : monad_fiber_task_t
{
    task()
        : monad_fiber_task_t{
              .resume =
                  +[](monad_fiber_task_t *this_) {
                      static_cast<task *>(this_)->resume_();
                  },
              .destroy = +[](monad_fiber_task_t *) {},
              .priority = 0}
    {
    }

    ~task()
    {
        EXPECT_TRUE(done);
    }

    bool repeat = false;
    bool done = false;

    void resume_()
    {
        resumed++;
        resumed.notify_all();

        if (!repeat) {
            repeat = true;
            this->priority = ::priority--;
            monad_fiber_scheduler_dispatch(&sched, this);
        }
        else {
            done = true;
        }
    }
};

struct snapshots_4
{
    std::atomic<std::uint64_t> id_source{0};
    std::atomic<std::uint64_t> pointer{0};

    static constexpr std::size_t size_per_thread = 65536;
    std::array<
        std::array<std::pair<std::int64_t, std::uint64_t>, size_per_thread>, 4u>
        state;

    std::atomic<std::size_t> invoked{0u};

    snapshots_4()
    {
        for (auto &s : state) {
            for (auto &st : s) {
                st = {INT64_MIN, UINT64_MAX};
            }
        }
    }

    struct snapshotter_t
    {
        std::uint64_t id;
        snapshots_4 &db;
        bool done = false;

        snapshotter_t(snapshots_4 &db)
            : id(db.id_source++)
            , db(db)
        {

            assert(id < 4);
        }

        void operator()(std::int64_t priority_) noexcept
        {
            db.invoked.fetch_add(1u, std::memory_order_acq_rel);
            if (done) {
                return; // no overflow plz
            }
            // 0 -> 2^0, 1 -> 2^16
            auto const offset = 1ull << (id * 16ull);
            auto const ptr =
                db.pointer.fetch_add(offset, std::memory_order_acq_rel);
            auto const idx = (ptr >> (id * 16ull)) & 0xFFFFull;

            if (idx == 0xFFFFu) {
                db.pointer -= offset; // so we're not len == 0
                done = true;
            }
            db.state[id][idx] = {priority_, ptr};
        }
    };

    snapshotter_t snap()
    {
        return snapshotter_t{*this};
    }
};

struct snapshots_8
{
    std::atomic<std::uint64_t> id_source{0};
    std::atomic<std::uint64_t> pointer{0};

    static constexpr std::size_t size_per_thread = 256;

    std::array<
        std::array<std::pair<std::int64_t, std::uint64_t>, size_per_thread>, 8u>
        state;

    std::atomic<std::size_t> invoked{0u};

    snapshots_8()
    {
        for (auto &s : state) {
            for (auto &st : s) {
                st = {INT64_MIN, UINT64_MAX};
            }
        }
    }

    struct snapshotter_t
    {
        std::uint64_t id;
        snapshots_8 &db;
        bool done = false;

        snapshotter_t(snapshots_8 &db)
            : id(db.id_source++)
            , db(db)
        {
            assert(id < 8);
        }

        void operator()(std::int64_t priority_)
        {
            db.invoked.fetch_add(1u, std::memory_order_acq_rel);
            if (done) {
                return; // no overflow plz
            }
            // 0 -> 2^0, 1 -> 2^8
            auto const offset = 1ull << (id * 8ull);

            auto const ptr =
                db.pointer.fetch_add(offset, std::memory_order_acq_rel);
            auto const idx = (ptr >> (id * 8ull)) & 0xFFull;

            if (idx == 0xFFu) {
                db.pointer -= offset; // so we're not len == 0
                done = true;
            }

            db.state[id][idx] = {priority_, ptr};
        }
    };

    snapshotter_t snap()
    {
        return snapshotter_t{*this};
    }
};

template <typename Func>
struct lambda_task : monad_fiber_task_t
{

    template <typename Func_>
    lambda_task(Func_ &&func, std::int64_t prio)
        : func(std::forward<Func_>(func))
    {
        this->resume = +[](monad_fiber_task_t *task) {
            auto lt = static_cast<lambda_task *>(task);
            lt->func();
            delete lt;
        };
        this->destroy = +[](monad_fiber_task_t *task) {
            delete static_cast<lambda_task *>(task);
        };
        this->priority = prio;
    }

    Func func;
};

template <typename Func>
lambda_task<std::decay_t<Func>> *make_lt(Func &&f, std::int64_t prio)
{
    return new lambda_task<std::decay_t<Func>>(std::forward<Func>(f), prio);
}

TEST(scheduler, post)
{
    bool ran = false;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);
    monad_fiber_scheduler_post(&s, make_lt([&] { ran = true; }, 0));
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    EXPECT_TRUE(ran);
}

TEST(scheduler, dispatch)
{
    bool ran = false;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);
    monad_fiber_scheduler_dispatch(&s, make_lt([&] { ran = true; }, 0));
    std::this_thread::yield();
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    EXPECT_TRUE(ran);
}

TEST(scheduler, post_dispatch_ordered)
{
    bool ran = false, ran2;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);
    monad_fiber_scheduler_post(
        &s,
        make_lt(
            [&] {
                ran = true;
                monad_fiber_scheduler_dispatch(
                    &s, make_lt([&] { ran2 = true; }, 0));
                EXPECT_TRUE(ran2);
            },
            1));
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    EXPECT_TRUE(ran);
}

TEST(scheduler, DISABLED_post_dispatch_prioritized)
{
    bool ran = false, ran2;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);
    monad_fiber_scheduler_post(
        &s,
        make_lt(
            [&] {
                ran = true;
                monad_fiber_scheduler_dispatch(
                    &s, make_lt([&] { ran2 = true; }, 1));
                EXPECT_FALSE(ran2);
            },
            0));
    monad_fiber_scheduler_destroy(&s);

    EXPECT_TRUE(ran);
    EXPECT_TRUE(ran2);
}

TEST(scheduler, post_post)
{
    std::atomic<bool> ran = false, ran2;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);
    monad_fiber_scheduler_post(
        &s,
        make_lt(
            [&] {
                ran = true;
                monad_fiber_scheduler_post(
                    &s,
                    make_lt(
                        [&] {
                            usleep(1000);
                            ran2 = true;
                        },
                        0));
                EXPECT_FALSE(ran2);
            },
            1));

    wait(s);
    monad_fiber_scheduler_destroy(&s);

    EXPECT_TRUE(ran);
    EXPECT_TRUE(ran2);
}

void check_sorted(snapshots_4 &ss)
{
    EXPECT_EQ(ss.invoked, (ss.size_per_thread - 1) * ss.state.size());

    // make sure it's ordered now.
    for (auto i = 0ull; i < 4ull; i++) {
        auto const &series = ss.state[i];
        auto const len = (ss.pointer.load() >> (i * 16ull)) & 0xFFFFull;
        ASSERT_GT(len, 0);
        auto const begin = series.begin(), end = series.begin() + len;
        ASSERT_LE(end, series.end());
        EXPECT_TRUE(std::is_sorted(begin, end));
        for (auto itr = std::next(begin); itr != end; itr++) {
            EXPECT_LT(std::prev(itr)->first, itr->first)
                << " of thread " << i << " at pos "
                << std::distance(begin, itr); // first = priority

            auto priority_ = itr->first;
            // check the others

            for (auto j = 0ull; j < 4ull; j++) {
                if (i == j) {
                    continue;
                }

                // we check what was completed before the current task.
                auto const idx =
                    (std::prev(itr)->second >> (j * 16ull)) & 0xFFFFull;

                // idx points to the current, so we need to decrement it as
                // well.
                if (idx < 2 || idx == 65535) {
                    continue;
                }
                EXPECT_LE(ss.state[j][idx - 1].first, priority_) // 32 is
                    << " of thread " << i << " at pos "
                    << std::distance(begin, itr) << " compared to thread " << j
                    << " at pos " << idx; // first = priority
            }
        }
    }
}

void check_sorted(snapshots_8 &ss)
{
    EXPECT_EQ(ss.invoked, (ss.size_per_thread - 1) * ss.state.size());

    // make sure it's ordered now.
    for (auto i = 0ull; i < ss.state.size(); i++) {
        auto const &series = ss.state[i];
        auto const len = (ss.pointer.load() >> (i * 8ull)) & 0xFFull;
        if (len == 0) {
            continue;
        }
        auto const begin = series.begin(), end = series.begin() + len;
        ASSERT_LE(end, series.end());
        EXPECT_TRUE(std::is_sorted(begin, end));
        for (auto itr = std::next(begin); itr != end; itr++) {
            EXPECT_LT(std::prev(itr)->first, itr->first)
                << " of thread " << i << " at pos "
                << std::distance(begin, itr); // first = priority

            auto priority_ = itr->first;
            // check the others

            for (auto j = 0ull; j < 8ull; j++) {
                if (i == j) {
                    continue;
                }

                // we check what was completed before the current task.
                auto const idx =
                    (std::prev(itr)->second >> (j * 8ull)) & 0xFFull;
                continue;

                // idx points to the current, so we need to decrement it as
                // well.
                if (idx < 2) {
                    continue;
                }
                EXPECT_LE(ss.state[j][idx - 1].first, priority_) // 32 is
                    << " of thread " << i << " at pos "
                    << std::distance(begin, itr) << " compared to thread " << j
                    << " at pos " << idx; // first = priority
            }
        }
    }
}

TEST(scheduler, DISABLED_ordered_4)
{
    static bool once = false;
    ASSERT_FALSE(once);
    once = true;
    snapshots_4 ss;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);

    std::shared_mutex mtx; // block all threads during posting
    mtx.lock();
    for (std::uint64_t i = 0ull; i < 4; i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&] {
                    mtx.lock_shared();
                    mtx.unlock_shared();
                },
                INT64_MIN));
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(10));

    for (std::int64_t i = 0; i < (std::int64_t)(4 * ss.size_per_thread) - 4;
         i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&, i] {
                    thread_local static auto s = ss.snap();
                    s(i);
                },
                i));
    }

    mtx.unlock();
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    check_sorted(ss);
}

TEST(scheduler, DISABLED_ordered_8)
{
    static bool once = false;
    ASSERT_FALSE(once);
    once = true;
    snapshots_8 ss;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 8, NULL);

    std::shared_mutex mtx; // block all threads during posting
    mtx.lock();
    for (std::uint64_t i = 0ull; i < 8; i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&] {
                    mtx.lock_shared();
                    mtx.unlock_shared();
                },
                INT64_MIN));
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(10));

    for (std::int64_t i = 0; i < (std::int64_t)(8 * ss.size_per_thread) - 8;
         i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&, i] {
                    thread_local static auto s = ss.snap();
                    s(i);
                },
                i));
    }

    mtx.unlock();
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    check_sorted(ss);
}

TEST(scheduler, DISABLED_inverted_4)
{
    static bool once = false;
    ASSERT_FALSE(once);
    once = true;
    snapshots_4 ss;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);

    std::shared_mutex mtx; // block all threads during posting
    mtx.lock();
    for (std::uint64_t i = 0ull; i < 4; i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&] {
                    mtx.lock_shared();
                    mtx.unlock_shared();
                },
                INT64_MIN));
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(10));

    for (std::int64_t i = (4 * ss.size_per_thread) - 4; i > 0; i--) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&, i] {
                    thread_local static auto s = ss.snap();
                    s(i);
                },
                i));
    }

    mtx.unlock();
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    check_sorted(ss);
}

TEST(scheduler, inverted_8)
{
    static bool once = false;
    ASSERT_FALSE(once);
    once = true;
    snapshots_8 ss;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 8, NULL);

    std::shared_mutex mtx; // block all threads during posting
    mtx.lock();
    for (std::uint64_t i = 0ull; i < 8; i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&] {
                    mtx.lock_shared();
                    mtx.unlock_shared();
                },
                INT64_MIN));
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(10));

    for (std::int64_t i = 0; i < (std::int64_t)(8 * ss.size_per_thread) - 8;
         i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&, i = -i] {
                    thread_local static auto s = ss.snap();
                    s(i);
                },
                -i));
    }

    mtx.unlock();
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    check_sorted(ss);
}

TEST(scheduler, DISABLED_split_4)
{
    static bool once = false;
    ASSERT_FALSE(once);
    once = true;
    snapshots_4 ss;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 4, NULL);

    std::shared_mutex mtx; // block all threads during posting
    mtx.lock();
    for (std::uint64_t i = 0ull; i < 4; i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&] {
                    mtx.lock_shared();
                    mtx.unlock_shared();
                },
                INT64_MIN));
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(10));

    for (std::int64_t i = (4 * ss.size_per_thread) - 4; i > 0; i--) {
        std::int64_t const j = i % 2 ? i : -i;
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&, j] {
                    thread_local static auto s = ss.snap();
                    s(j);
                },
                j));
    }

    mtx.unlock();
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    check_sorted(ss);
}

TEST(scheduler, split_8)
{
    static bool once = false;
    ASSERT_FALSE(once);
    once = true;
    snapshots_8 ss;

    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 8, NULL);

    std::shared_mutex mtx; // block all threads during posting
    mtx.lock();
    for (std::uint64_t i = 0ull; i < 8; i++) {
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&] {
                    mtx.lock_shared();
                    mtx.unlock_shared();
                },
                INT64_MIN));
    }

    std::this_thread::sleep_for(std::chrono::milliseconds(10));

    for (std::int64_t i = 0; i < (std::int64_t)(8 * ss.size_per_thread) - 8;
         i++) {
        std::int64_t const j = i % 2 ? i : -i;
        monad_fiber_scheduler_post(
            &s,
            make_lt(
                [&, j] {
                    thread_local static auto s = ss.snap();
                    s(j);
                },
                j));
    }
    mtx.unlock();
    wait(s);
    monad_fiber_scheduler_destroy(&s);

    check_sorted(ss);
}
