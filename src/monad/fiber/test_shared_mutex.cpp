#include <chrono>

#include <monad/fiber/shared_mutex.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json.hpp>

// an empty mutex implementation should optimize away
struct DumbMutex
{
    void lock() {}

    [[nodiscard]] bool try_lock() { return true; }

    void unlock() {}

    void lock_shared() {}

    [[nodiscard]] bool try_lock_shared() { return true; }

    void unlock_shared() {}
};

template <typename TMutex>
class Counter
{
public:
    [[nodiscard]] uint64_t get() const
    {
        std::shared_lock<TMutex> lock{mutex_};
        return counter_;
    }

    [[nodiscard]] uint64_t increment()
    {
        std::unique_lock<TMutex> lock{mutex_};
        auto old = counter_;
        counter_++;
        return old;
    }

private:
    uint64_t counter_{1};
    mutable TMutex mutex_;
};

template <typename>
struct SharedMutex : public testing::Test
{
};

using MutexTypes =
    ::testing::Types<DumbMutex, monad::shared_mutex, std::shared_mutex>;

TYPED_TEST_SUITE(SharedMutex, MutexTypes);

TYPED_TEST(SharedMutex, DISABLED_simple_bench)
{
    Counter<TypeParam> counter;
    uint64_t volatile NUM_READS = 10'000'000;
    auto min_time = std::numeric_limits<int64_t>::max();

    uint64_t accum = 0;

    for (size_t iter = 0; iter < 5; iter++) {
        auto before = std::chrono::steady_clock::now();
        for (size_t i = 0; i < NUM_READS; i++) {
            accum += counter.get();
        }
        auto after = std::chrono::steady_clock::now();
        min_time = std::min(
            min_time,
            std::chrono::duration_cast<std::chrono::nanoseconds>(after - before)
                .count());
    }

    nlohmann::json res = nlohmann::json::object();
    res["num_threads"] = 1;
    res["num_fibers"] = 1;
    res["num_reads"] = NUM_READS;
    res["time"] = min_time;
    res["accum"] = accum;
    std::cout << res.dump() << std::endl;
}

TEST(MutexCorrectness, many_readers)
{
    Counter<monad::shared_mutex> counter;
    (void)counter.increment();

    {
        std::vector<std::jthread> threads;
        for (size_t thread = 0; thread < 8; thread++) {
            threads.emplace_back([&] mutable {
                std::vector<boost::fibers::fiber> fibers;
                for (size_t fiber = 0; fiber < 8; fiber++) {
                    fibers.emplace_back(
                        [&] mutable { EXPECT_EQ(counter.get(), 2); });
                }

                for (auto &fiber : fibers) {
                    fiber.join();
                }
            });
        }
    }
}

TEST(MutexCorrectness, many_readers_and_writers)
{
    Counter<monad::shared_mutex> counter;
    (void)counter.increment();

    {
        std::vector<std::jthread> threads;
        for (size_t thread = 0; thread < 8; thread++) {
            threads.emplace_back([&] mutable {
                std::vector<boost::fibers::fiber> fibers;
                for (size_t fiber = 0; fiber < 8; fiber++) {
                    // just EXPECT > 0 so it does not get optimized away
                    if (fiber % 2) {
                        fibers.emplace_back(
                            [&] mutable { EXPECT_GT(counter.get(), 0); });
                    }
                    else {
                        fibers.emplace_back(
                            [&] mutable { EXPECT_GT(counter.increment(), 0); });
                    }
                }
                for (auto &fiber : fibers) {
                    fiber.join();
                }
            });
        }
    }

    EXPECT_EQ(counter.get(), 34);
}
