#include <chrono>

#include <monad/fiber/shared_mutex.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json.hpp>

#include <boost/core/demangle.hpp>

#include <monad/logging/formatter.hpp>

#define ANKERL_NANOBENCH_IMPLEMENT
#include <nanobench.h>

// an empty mutex implementation should optimize away
struct NoLockingMutex
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
        if constexpr (requires(TMutex m) {
                          {
                              m.lock_shared()
                          } -> std::convertible_to<void>;
                      }) {
            std::shared_lock<TMutex> lock{mutex_};
            return counter_;
        }
        else {
            std::unique_lock<TMutex> lock{mutex_};
            return counter_;
        }
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

ankerl::nanobench::Bench SHARED_MUTEX_BENCH = [] {
    ankerl::nanobench::Bench bench;
    bench.title("read counter lock_shared() call");
    bench.relative(true);
    bench.performanceCounters(true);
    return bench;
}();

template <typename>
struct SharedMutex : public testing::Test
{
};

using MutexTypes = ::testing::Types<
    NoLockingMutex, monad::shared_mutex, boost::fibers::mutex,
    std::shared_mutex, std::mutex, std::timed_mutex, std::shared_timed_mutex>;

TYPED_TEST_SUITE(SharedMutex, MutexTypes);

TYPED_TEST(SharedMutex, simple_bench)
{
    Counter<TypeParam> counter;
    uint64_t accum = 0;
    SHARED_MUTEX_BENCH
        .run(
            fmt::format("{}", boost::core::demangle(typeid(TypeParam).name())),
            [&] { accum += counter.get(); })
        .doNotOptimizeAway(accum);
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
