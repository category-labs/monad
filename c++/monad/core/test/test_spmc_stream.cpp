#include <gtest/gtest.h>
#include <monad/core/spmc_stream.h>

#include <cstring>
#include <thread>

TEST(SpmcStream, single_consumer)
{
    auto const path = "spmc_" + std::to_string(getpid());
    auto *pqueue = spmc_stream_create(path.c_str(), true);
    ASSERT_NE(pqueue, nullptr);

    auto *cqueue = spmc_stream_create(path.c_str(), false);
    ASSERT_NE(cqueue, nullptr);

    struct Output
    {
        unsigned long long seq;
        char buf[1024];
    } out;

    auto const handler = [](unsigned long long const seq,
                            void const volatile *const buf,
                            size_t const size,
                            void *const context) {
        auto &out = *reinterpret_cast<Output *>(context);
        out.seq = seq;
        ASSERT_LE(size, sizeof(Output::buf));
        for (size_t i = 0; i < size; ++i) {
            out.buf[i] = ((char const volatile *)buf)[i];
        }
    };

    EXPECT_EQ(spmc_stream_pop(cqueue, handler, (void *)&out), EAGAIN);

    char const buf[] = "anago";
    spmc_stream_write(pqueue, buf, sizeof(buf));
    spmc_stream_push(pqueue);

    EXPECT_EQ(spmc_stream_pop(cqueue, handler, (void *)&out), 0);
    EXPECT_EQ(out.seq, 2);
    EXPECT_STREQ(out.buf, "anago");

    EXPECT_EQ(spmc_stream_pop(cqueue, handler, (void *)&out), EAGAIN);

    char const buf2[] = "molandak";
    spmc_stream_write(pqueue, buf2, sizeof(buf2));
    spmc_stream_push(pqueue);

    EXPECT_EQ(spmc_stream_pop(cqueue, handler, (void *)&out), 0);
    EXPECT_EQ(out.seq, 4);
    EXPECT_STREQ(out.buf, "molandak");

    spmc_stream_destroy(pqueue);
    spmc_stream_destroy(cqueue);
}

TEST(SpmcStream, write_multiple)
{
    auto const path = "spmc_" + std::to_string(getpid());
    auto *pqueue = spmc_stream_create(path.c_str(), true);
    ASSERT_NE(pqueue, nullptr);

    auto *cqueue = spmc_stream_create(path.c_str(), false);
    ASSERT_NE(cqueue, nullptr);

    struct Output
    {
        unsigned long long seq;
        char buf[1024];
    } out;

    auto const handler = [](unsigned long long const seq,
                            void const volatile *const buf,
                            size_t const size,
                            void *const context) {
        auto &out = *reinterpret_cast<Output *>(context);
        out.seq = seq;
        ASSERT_LE(size, sizeof(Output::buf));
        for (size_t i = 0; i < size; ++i) {
            out.buf[i] = ((char const volatile *)buf)[i];
        }
    };

    char const buf[] = "anago";
    char const buf2[] = "molandak";
    spmc_stream_write(pqueue, buf, sizeof(buf) - 1);
    spmc_stream_write(pqueue, buf2, sizeof(buf2));
    spmc_stream_push(pqueue);

    EXPECT_EQ(spmc_stream_pop(cqueue, handler, (void *)&out), 0);
    EXPECT_EQ(out.seq, 2);
    EXPECT_STREQ(out.buf, "anagomolandak");

    spmc_stream_destroy(pqueue);
    spmc_stream_destroy(cqueue);
}

TEST(SpmcStream, multiple_consumer)
{
    auto const path = "spmc_" + std::to_string(getpid());
    auto *pqueue = spmc_stream_create(path.c_str(), true);
    ASSERT_NE(pqueue, nullptr);

    auto *cqueue1 = spmc_stream_create(path.c_str(), false);
    ASSERT_NE(cqueue1, nullptr);

    auto *cqueue2 = spmc_stream_create(path.c_str(), false);
    ASSERT_NE(cqueue2, nullptr);

    struct Output
    {
        unsigned long long seq;
        char buf[1024];
    } out;

    auto const handler = [](unsigned long long const seq,
                            void const volatile *const buf,
                            size_t const size,
                            void *const context) {
        auto &out = *reinterpret_cast<Output *>(context);
        out.seq = seq;
        ASSERT_LE(size, sizeof(Output::buf));
        for (size_t i = 0; i < size; ++i) {
            out.buf[i] = ((char const volatile *)buf)[i];
        }
    };

    EXPECT_EQ(spmc_stream_pop(cqueue1, handler, (void *)&out), EAGAIN);
    EXPECT_EQ(spmc_stream_pop(cqueue2, handler, (void *)&out), EAGAIN);

    char const buf[] = "chog";
    spmc_stream_write(pqueue, buf, sizeof(buf));
    spmc_stream_push(pqueue);

    EXPECT_EQ(spmc_stream_pop(cqueue1, handler, (void *)&out), 0);
    EXPECT_EQ(out.seq, 2);
    EXPECT_STREQ(out.buf, "chog");

    EXPECT_EQ(spmc_stream_pop(cqueue2, handler, (void *)&out), 0);
    EXPECT_EQ(out.seq, 2);
    EXPECT_STREQ(out.buf, "chog");

    EXPECT_EQ(spmc_stream_pop(cqueue1, handler, (void *)&out), EAGAIN);
    EXPECT_EQ(spmc_stream_pop(cqueue2, handler, (void *)&out), EAGAIN);

    spmc_stream_destroy(pqueue);
    spmc_stream_destroy(cqueue1);
    spmc_stream_destroy(cqueue2);
}

TEST(SpmcStream, threads)
{
    constexpr auto N = 1000;
    auto const path = "spmc_" + std::to_string(getpid());
    auto const consumer = [&] {
        SpmcStream *stream = spmc_stream_create(path.c_str(), false);
        while (stream == nullptr) {
            stream = spmc_stream_create(path.c_str(), false);
        }

        struct Output
        {
            unsigned long long seq;
            uint32_t element;
        } out;

        auto const handler = [](unsigned long long const seq,
                                void const volatile *const buf,
                                size_t const size,
                                void *const context) {
            auto &out = *reinterpret_cast<Output *>(context);
            out.seq = seq;
            ASSERT_LE(size, sizeof(Output::element));
            char obuf[sizeof(Output::element)];
            for (size_t i = 0; i < size; ++i) {
                obuf[i] = ((char const volatile *)buf)[i];
            }
            std::memcpy(&out.element, obuf, sizeof(Output::element));
        };

        for (size_t i = 0; i < N; ++i) {
            auto const res = spmc_stream_pop(stream, handler, (void *)&out);
            if (res == EAGAIN) {
                continue;
            }
            else if (res == ECANCELED) {
                EXPECT_GE(out.seq, i * 2);
                continue;
            }
            EXPECT_EQ(out.element, out.seq / 2 - 1);
        }
        spmc_stream_destroy(stream);
    };

    SpmcStream *const stream = spmc_stream_create(path.c_str(), true);
    std::thread c1(consumer);
    std::thread c2(consumer);
    std::thread p([&] {
        ASSERT_NE(stream, nullptr);
        for (uint32_t i = 0; i < N; ++i) {
            spmc_stream_write(stream, &i, sizeof(i));
            spmc_stream_push(stream);
        }
        spmc_stream_destroy(stream);
    });

    c1.join();
    c2.join();
    p.join();
}
