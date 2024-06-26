#include <gtest/gtest.h>

#include <monad/fiber/assert.h>
#include <monad/fiber/current.h>

#include <thread>

TEST(current, DISABLED_fiber_main)
{
    monad_fiber_init_main();
    monad_fiber_t *mm = monad_fiber_main(), th1 = {}, th2 = {};

    std::thread{[&] {
        monad_fiber_init_main();
        auto f = monad_fiber_main();
        th1 = *f;
        EXPECT_NE(monad_fiber_main(), mm);
        EXPECT_TRUE(monad_fiber_is_main(f));
    }}.join();
    std::thread{[&] {
        monad_fiber_init_main();
        auto f = monad_fiber_main();
        th2 = *f;
        EXPECT_NE(monad_fiber_main(), mm);
        EXPECT_TRUE(monad_fiber_is_main(f));
    }}.join();

    EXPECT_EQ(mm->task.priority, th1.task.priority);
    EXPECT_EQ(mm->task.priority, th2.task.priority);
    EXPECT_EQ(mm->task.resume, th1.task.resume);
    EXPECT_EQ(mm->task.resume, th2.task.resume);

    EXPECT_TRUE(monad_fiber_is_main(mm));
}

extern "C" monad_fiber_t *
monad_fiber_activate_fiber(monad_fiber_t *new_current);

TEST(current, DISABLED_switch_)
{
    monad_fiber_init_main();
    monad_fiber_t *mf = monad_fiber_main();

    monad_fiber_scheduler shed;
    monad_fiber_scheduler_create(&shed, 0, NULL);

    monad_fiber_t mft = {
        .task = {.resume = NULL, .destroy = NULL, .priority = -1ll},
        .context = nullptr,
        .scheduler = &shed};

    auto l = [&](monad_fiber_context_t *fb,
                 monad_fiber_context_t *from) -> monad_fiber_context_t * {
        MONAD_ASSERT(from->fiber != NULL);
        mft.context = fb;
        monad_fiber_set_name(fb, "switch_test_fiber");
        auto m = monad_fiber_activate_fiber(&mft);
        assert(m == monad_fiber_main());
        assert(from->fiber != NULL);
        monad_fiber_switch_to_main();
        assert(from->fiber != NULL);
        monad_fiber_activate_fiber(m); // preemptively go back to main.
        assert(from->fiber != NULL);
        return from;
    };

    mft.context = monad_fiber_context_callcc(
        mf->context,
        4096,
        false,
        +[](void *ptr,
            monad_fiber_context_t *fb,
            monad_fiber_context_t *from) -> monad_fiber_context_t * {
            return (*static_cast<decltype(l) *>(ptr))(fb, from);
        },
        &l);

    mf->scheduler = &shed;
    monad_fiber_activate_fiber(monad_fiber_main());
    monad_fiber_switch_to_fiber(&mft);
    monad_fiber_scheduler_destroy(&shed);
    mf->scheduler = NULL;
}

TEST(current, yield_to_task)
{
    monad_fiber_scheduler shed;
    monad_fiber_scheduler_create(&shed, 0, &monad_fiber_init_main);
    monad_fiber_init_main();
    monad_fiber_main()->scheduler = &shed;
    monad_fiber_t *mf = monad_fiber_main();

    struct my_task : monad_fiber_task
    {
        bool ran = false;

        void resume()
        {
            ASSERT_FALSE(ran);
            ran = true;
        }

        explicit my_task(std::int64_t priority)
            : monad_fiber_task{
                  .resume =
                      +[](monad_fiber_task *this_) {
                          static_cast<my_task *>(this_)->resume();
                      },
                  .destroy =
                      +[](monad_fiber_task *) {
                          ASSERT_EQ("Musten't be reached", nullptr);
                      },
                  .priority = priority}
        {
        }
    };

    my_task t1{1}, t2{-1}, t3{0};

    monad_fiber_yield(); // this will do nothing
    t1.priority = 1;
    monad_fiber_scheduler_post(&shed, &t1);

    monad_fiber_yield(); // this will do nothing, because it's the same priority
    EXPECT_FALSE(t1.ran);

    monad_fiber_scheduler_post(&shed, &t2);
    monad_fiber_yield(); // this should run , higher priority
    EXPECT_TRUE(t2.ran);

    monad_fiber_scheduler_post(&shed, &t3);
    monad_fiber_yield(); // this should run one, since it's the same priority
                         // and we're yielding
    EXPECT_TRUE(t3.ran);

    mf->scheduler = &shed;

    monad_fiber_yield(); // this will run the
    monad_fiber_scheduler_destroy(&shed);
    mf->scheduler = NULL;
}

void awaitable_sleep(monad_fiber_t *to_resume, void *us_)
{
    std::thread{[us = reinterpret_cast<std::uintptr_t>(us_), to_resume] {
        usleep(static_cast<useconds_t>(us));
        monad_fiber_scheduler_dispatch(to_resume->scheduler, &to_resume->task);
    }}.detach();
};

TEST(current, DISABLED_await_from_thread)
{
    monad_fiber_scheduler shed;
    monad_fiber_scheduler_create(&shed, 0, NULL);
    monad_fiber_init_main();
    monad_fiber_main()->scheduler = &shed;
    monad_fiber_set_name(monad_fiber_main()->context, "await_from_thread_test");
    useconds_t const us = 1000;

    bool ran = false;

    monad_fiber_t mft = {
        .task = {.resume = nullptr, .destroy = nullptr, .priority = -1ll},
        .context = nullptr,
        .scheduler = &shed};

    auto l = [&](monad_fiber_context_t *fb,
                 monad_fiber_context_t *from) -> monad_fiber_context_t * {
        mft.context = fb;
        monad_fiber_set_name(fb, "await_from_thread_task");
        auto m = monad_fiber_activate_fiber(&mft);
        MONAD_ASSERT(m == monad_fiber_main());
        monad_fiber_switch_to_main();
        assert(&mft == monad_fiber_current());

        monad_fiber_await(&awaitable_sleep, reinterpret_cast<void *>(us));
        ran = true;
        monad_fiber_scheduler_stop(&shed);
        return from;
    };

    mft.context = monad_fiber_context_callcc(
        monad_fiber_main()->context,
        4096,
        false,
        +[](void *ptr,
            monad_fiber_context_t *fb,
            monad_fiber_context_t *from) -> monad_fiber_context_t * {
            return (*static_cast<decltype(l) *>(ptr))(fb, from);
        },
        &l);

    monad_fiber_activate_fiber(monad_fiber_main());

    monad_fiber_scheduler_post(&shed, &mft.task);
    mft.task.resume = [](monad_fiber_task_t *task) {
        monad_fiber_switch_to_fiber(reinterpret_cast<monad_fiber_t *>(task));
    };
    EXPECT_FALSE(ran);

    monad_fiber_scheduler_work(&shed);
    EXPECT_TRUE(ran);
}

TEST(current, DISABLED_monad_fiber_create_noop)
{
    monad_fiber_init_main();
    auto f = monad_fiber_create(4096, true, NULL, +[](void *) {}, NULL);

    EXPECT_EQ(f, nullptr);
}

TEST(current, monad_fiber_create_switch_once)
{
    monad_fiber_init_main();
    int pos = 0;
    auto f = monad_fiber_create(
        4096,
        true,
        NULL,
        +[](void *pos_) {
            int &pos = *static_cast<int *>(pos_);
            pos = 1;
            monad_fiber_switch_to_main();
            pos = 2;
        },
        &pos);

    EXPECT_NE(f, nullptr);
    EXPECT_EQ(pos, 1);

    monad_fiber_switch_to_fiber(f);
    EXPECT_EQ(pos, 2); // should be destroyed now
    EXPECT_EQ(monad_fiber_main(), monad_fiber_current());
}

TEST(current, DISABLED_monad_fiber_create_destroy)
{
    monad_fiber_init_main();
    int pos = 0;
    auto f = monad_fiber_create(
        4096,
        true,
        NULL,
        +[](void *pos_) {
            int &pos = *static_cast<int *>(pos_);
            pos = 1;
            monad_fiber_switch_to_main();
            pos = 2;
        },
        &pos);

    EXPECT_NE(f, nullptr);
    EXPECT_EQ(pos, 1);

    f->task.destroy(&f->task);
    EXPECT_EQ(pos, 1); // should be skipped
    EXPECT_EQ(monad_fiber_main(), monad_fiber_current());
}

TEST(current, monad_fiber_create_self_destroy)
{
    monad_fiber_init_main();
    int pos = 0;
    auto f = monad_fiber_create(
        4096,
        true,
        NULL,
        +[](void *pos_) {
            int &pos = *static_cast<int *>(pos_);
            pos = 1;
            monad_fiber_current()->task.destroy(&monad_fiber_current()->task);
            pos = 2;
        },
        &pos);

    EXPECT_EQ(f, nullptr);
    EXPECT_EQ(pos, 1);
}
