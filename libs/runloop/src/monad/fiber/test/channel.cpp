#include <gtest/gtest.h>

#include <monad/fiber/channel.h>

void wait(monad_fiber_scheduler_t &s);

TEST(channel, DISABLED_try_buffered)
{
    monad_fiber_channel ch;
    monad_fiber_channel_create(&ch, 2, sizeof(int));

    int value = -1;
    EXPECT_FALSE(monad_fiber_channel_try_read(&ch, &value));
    EXPECT_EQ(value, -1);
    value = 42;
    EXPECT_TRUE(monad_fiber_channel_try_write(&ch, &value));
    value = 43;
    EXPECT_TRUE(monad_fiber_channel_try_write(&ch, &value));
    value = 0;
    EXPECT_FALSE(monad_fiber_channel_try_write(&ch, &value));
    EXPECT_TRUE(monad_fiber_channel_try_read(&ch, &value));
    EXPECT_EQ(value, 42);
    EXPECT_TRUE(monad_fiber_channel_try_read(&ch, &value));
    EXPECT_EQ(value, 43);
    EXPECT_FALSE(monad_fiber_channel_try_read(&ch, &value));
    monad_fiber_channel_destroy(&ch);
}

TEST(channel, try_unbuffered)
{
    monad_fiber_channel ch;
    monad_fiber_channel_create(&ch, 0, sizeof(int));

    int value = -1;
    EXPECT_FALSE(monad_fiber_channel_try_read(&ch, &value));
    EXPECT_FALSE(monad_fiber_channel_try_write(&ch, &value));
    monad_fiber_channel_destroy(&ch);
}

extern thread_local monad_fiber_t *monad_fiber_current_;

TEST(channel, DISABLED_buffered_equal)
{
    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 8, &monad_fiber_init_main);

    monad_fiber_current_ = NULL;

    monad_fiber_init_main();
    monad_fiber_main()->scheduler = &s;
    monad_fiber_channel_t ch;
    monad_fiber_channel_create(&ch, 1, sizeof(int));

    static std::atomic_bool writer_done{false}, reader_done{false};
    writer_done = reader_done = false;

    struct notifier
    {
        std::atomic_bool &done;

        notifier(std::atomic_bool &done)
            : done(done)
        {
        }

        ~notifier()
        {
            done.store(true, std::memory_order_release);
        }
    };

    auto w = monad_fiber_create(
        1024 * 256,
        true,
        &s,
        +[](void *ch_) noexcept {
            monad_fiber_set_name(monad_fiber_current()->context, "writer");
            monad_fiber_current()->task.priority = -1;

            notifier _{writer_done};
            auto ch = static_cast<monad_fiber_channel_t *>(ch_);
            int i = 0;
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 1)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 2)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 3)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 4)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 5)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 6)), EPIPE);
        },
        &ch);

    EXPECT_EQ(w->scheduler, &s);

    ASSERT_TRUE(ch.pending_writes != NULL);

    auto r = monad_fiber_create(
        1024 * 256,
        true,
        &s,
        +[](void *ch_) noexcept {
            monad_fiber_set_name(monad_fiber_current()->context, "reader");
            monad_fiber_current()->task.priority = -1;
            notifier _{reader_done};
            int res = 0;
            auto ch = static_cast<monad_fiber_channel_t *>(ch_);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 1);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 2);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 3);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 4);
        },
        &ch);

    EXPECT_EQ(r->scheduler, &s);

    while (!reader_done) {
        monad_fiber_run_one(&s);
    }
    monad_fiber_channel_close(&ch);
    while (!writer_done) {
        monad_fiber_run_one(&s);
    }

    monad_fiber_channel_destroy(&ch);
    monad_fiber_scheduler_stop(&s);
    monad_fiber_scheduler_destroy(&s);
}

TEST(channel, DISABLED_buffered_writer_first)
{
    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 8, &monad_fiber_init_main);

    monad_fiber_current_ = NULL;

    monad_fiber_init_main();
    monad_fiber_main()->scheduler = &s;
    monad_fiber_channel_t ch;
    monad_fiber_channel_create(&ch, 1, sizeof(int));

    static std::atomic_bool writer_done{false}, reader_done{false};
    writer_done = reader_done = false;

    struct notifier
    {
        std::atomic_bool &done;

        notifier(std::atomic_bool &done)
            : done(done)
        {
        }

        ~notifier()
        {
            done.store(true, std::memory_order_release);
        }
    };

    auto w = monad_fiber_create(
        1024 * 256,
        true,
        &s,
        +[](void *ch_) noexcept {
            monad_fiber_set_name(monad_fiber_current()->context, "writer");
            monad_fiber_current()->task.priority = -2;
            notifier _{writer_done};
            auto ch = static_cast<monad_fiber_channel_t *>(ch_);
            int i = 0;
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 1)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 2)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 3)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 4)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 5)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 6)), EPIPE);
        },
        &ch);

    EXPECT_EQ(w->scheduler, &s);
    ASSERT_TRUE(ch.pending_writes != NULL);

    auto r = monad_fiber_create(
        1024 * 256,
        true,
        &s,
        +[](void *ch_) noexcept {
            monad_fiber_current()->task.priority = -1;
            monad_fiber_set_name(monad_fiber_current()->context, "reader");

            notifier _{reader_done};
            int res = 0;
            auto ch = static_cast<monad_fiber_channel_t *>(ch_);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 1);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 2);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 3);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 4);
        },
        &ch);

    EXPECT_EQ(r->scheduler, &s);

    while (!reader_done) {
        monad_fiber_yield();
    }
    monad_fiber_channel_close(&ch);
    while (!writer_done) {
        monad_fiber_yield();
    }

    monad_fiber_channel_destroy(&ch);
    monad_fiber_scheduler_stop(&s);
    monad_fiber_scheduler_destroy(&s);
}

TEST(channel, DISABLED_buffered_reader_first)
{
    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 8, &monad_fiber_init_main);

    monad_fiber_current_ = NULL;

    monad_fiber_init_main();
    monad_fiber_main()->scheduler = &s;
    monad_fiber_channel_t ch;
    monad_fiber_channel_create(&ch, 1, sizeof(int));

    static std::atomic_bool writer_done{false}, reader_done{false};
    writer_done = reader_done = false;

    struct notifier
    {
        std::atomic_bool &done;

        notifier(std::atomic_bool &done)
            : done(done)
        {
        }

        ~notifier()
        {
            done.store(true, std::memory_order_release);
        }
    };

    auto w = monad_fiber_create(
        1024 * 256,
        true,
        &s,
        +[](void *ch_) noexcept {
            monad_fiber_current()->task.priority = -1;
            notifier _{writer_done};
            auto ch = static_cast<monad_fiber_channel_t *>(ch_);
            int i = 0;
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 1)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 2)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 3)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 4)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 5)), 0);
            ASSERT_EQ(monad_fiber_channel_write(ch, &(i = 6)), EPIPE);
        },
        &ch);

    monad_fiber_set_name(w->context, "writer");
    EXPECT_EQ(w->scheduler, &s);

    ASSERT_TRUE(ch.pending_writes != NULL);

    auto r = monad_fiber_create(
        1024 * 256,
        true,
        &s,
        +[](void *ch_) noexcept {
            monad_fiber_current()->task.priority = -2;
            notifier _{reader_done};
            int res = 0;

            auto ch = static_cast<monad_fiber_channel_t *>(ch_);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 1);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 2);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 3);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 4);
        },
        &ch);

    monad_fiber_set_name(r->context, "reader");
    EXPECT_EQ(r->scheduler, &s);

    while (!reader_done) {
        monad_fiber_yield();
    }

    monad_fiber_channel_close(&ch);

    while (!writer_done) {
        monad_fiber_yield();
    }

    monad_fiber_channel_destroy(&ch);
    monad_fiber_scheduler_stop(&s);
    monad_fiber_scheduler_destroy(&s);
}

TEST(channel, DISABLED_send)
{
    monad_fiber_scheduler_t s;
    monad_fiber_scheduler_create(&s, 8, &monad_fiber_init_main);

    monad_fiber_current_ = NULL;

    monad_fiber_init_main();
    monad_fiber_main()->scheduler = &s;
    monad_fiber_channel_t ch;
    monad_fiber_channel_create(&ch, 1, sizeof(int));

    static std::atomic_bool reader_done{false};
    reader_done = false;

    struct notifier
    {
        std::atomic_bool &done;

        notifier(std::atomic_bool &done)
            : done(done)
        {
        }

        ~notifier()
        {
            done.store(true, std::memory_order_release);
        }
    };

    auto r = monad_fiber_create(
        1024 * 256,
        true,
        &s,
        +[](void *ch_) noexcept {
            monad_fiber_current()->task.priority = -2;
            notifier _{reader_done};
            int res = 0;

            auto ch = static_cast<monad_fiber_channel_t *>(ch_);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 1);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 2);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 3);
            EXPECT_EQ(monad_fiber_channel_read(ch, &res), 0);
            EXPECT_EQ(res, 4);
        },
        &ch);

    EXPECT_NE(r, nullptr);

    int i = 0;
    ASSERT_EQ(monad_fiber_channel_send(&ch, &(i = 1)), 0);
    ASSERT_EQ(monad_fiber_channel_send(&ch, &(i = 2)), 0);
    ASSERT_EQ(monad_fiber_channel_send(&ch, &(i = 3)), 0);
    ASSERT_EQ(monad_fiber_channel_send(&ch, &(i = 4)), 0);
    ASSERT_EQ(monad_fiber_channel_send(&ch, &(i = 5)), 0);

    ASSERT_TRUE(ch.pending_writes != NULL);

    while (!reader_done) {
        monad_fiber_yield();
    }

    //  monad_fiber_channel_close(&ch);
    monad_fiber_channel_destroy(&ch);
    monad_fiber_scheduler_stop(&s);
    monad_fiber_scheduler_destroy(&s);
}
