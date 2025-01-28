#include <gtest/gtest.h>

#include "../sorted_ring_buffer.h"

#include <monad/core/assert.h>
#include <monad/core/small_prng.hpp>

#include <chrono>
#include <iostream>
#include <set>

/*
1024 items did inf inserts/sec.
2048 items did inf inserts/sec.
4096 items did inf inserts/sec.
8192 items did 5.516e+06 inserts/sec.
16384 items did 2.1876e+06 inserts/sec.
32768 items did 1.20756e+06 inserts/sec.
65536 items did 949978 inserts/sec.
131072 items did 512924 inserts/sec.
262144 items did 257317 inserts/sec.
524288 items did 126628 inserts/sec.
*/

struct item
{
    uint32_t key, value;

    constexpr bool operator<(item const &o) const noexcept
    {
        return key < o.key;
    }
};

SORTED_RING_BUFFER_DECLARE(item);

TEST(sorted_ring_buffer, works)
{
    using sorted_ring_buffer_type = SORTED_RING_BUFFER_TYPE(item);
    sorted_ring_buffer_type rb = SORTED_RING_BUFFER_INIT(item, 16);
    std::set<item> keys;
    monad::small_prng rand;
    for (size_t n = 0; n < 64; n++) {
        auto const k = rand(), v = rand();
        const struct item i = {.key = k, .value = v};
        keys.insert(i);
        MONAD_ASSERT(SORTED_RING_BUFFER_INSERT(rb, i, true));
        SORTED_RING_BUFFER_CHECK_IF_NDEBUG(rb);
    }
    for (auto it = keys.begin(); it != keys.end();) {
        const struct item *i = SORTED_RING_BUFFER_FRONT(rb);
        EXPECT_EQ(i->key, it->key);
        EXPECT_EQ(i->value, it->value);
        it = keys.erase(keys.begin());
        SORTED_RING_BUFFER_POP_FRONT(rb);
    }
    for (size_t n = 0; n < 4096; n++) {
        auto const k = rand(), v = rand();
        const struct item i = {.key = k, .value = v};
        keys.insert(i);
        MONAD_ASSERT(SORTED_RING_BUFFER_INSERT(rb, i, true));
        SORTED_RING_BUFFER_CHECK_IF_NDEBUG(rb);
        if ((i.key & 3) != 0) {
            keys.erase(keys.begin());
            SORTED_RING_BUFFER_POP_FRONT(rb);
        }
    }
    for (auto it = keys.begin(); it != keys.end();) {
        const struct item *i = SORTED_RING_BUFFER_FRONT(rb);
        EXPECT_EQ(i->key, it->key);
        EXPECT_EQ(i->value, it->value);
        it = keys.erase(keys.begin());
        SORTED_RING_BUFFER_POP_FRONT(rb);
    }

    struct measurement
    {
        std::chrono::steady_clock::duration duration;
        uint32_t inserts{0}, pops{0};
    };

    std::vector<uint32_t> randomness;
    for (size_t n = 0; n < 1024 * 1024; n++) {
        randomness.push_back(rand());
    }
    uint32_t mux = rand();
    auto it = randomness.cbegin();
    std::vector<measurement> times;
    times.reserve(32);
#ifdef NDEBUG
    constexpr size_t MAX_COUNT = 1024 * 1024;
#else
    constexpr size_t MAX_COUNT = 128 * 1024;
#endif
    for (size_t count = 1024; count < MAX_COUNT; count <<= 1) {
        std::cout << "Benchmarking " << count << " items ..." << std::endl;
        auto const begin = std::chrono::steady_clock::now();
        measurement meas;
        while (SORTED_RING_BUFFER_SIZE(rb) < count) {
            auto const k = mux ^ *it++;
            if (it == randomness.cend()) {
                mux = rand();
                it = randomness.cbegin();
            }
            const struct item i = {.key = k, .value = 0};
            MONAD_ASSERT(SORTED_RING_BUFFER_INSERT(rb, i, true));
            meas.inserts++;
            SORTED_RING_BUFFER_CHECK_IF_NDEBUG(rb);
            if ((i.key & 3) == 0) {
                SORTED_RING_BUFFER_POP_FRONT(rb);
                meas.pops++;
            }
        }
        auto const end = std::chrono::steady_clock::now();
        meas.duration = end - begin;
        times.push_back(meas);
    }
    auto it2 = times.cbegin();
    for (size_t count = 1024; count < MAX_COUNT; count <<= 1) {
        std::cout << count << " items did "
                  << (1000.0 * double(it2->inserts) /
                      double(
                          std::chrono::duration_cast<std::chrono::milliseconds>(
                              it2->duration)
                              .count()))
                  << " inserts/sec." << std::endl;
        ++it2;
    }

    SORTED_RING_BUFFER_DESTROY(rb);
}
