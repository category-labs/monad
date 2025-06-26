#include "ticks_count.h"

#include "ticks_count_impl.h"

#include <chrono>

extern "C" monad_cpu_ticks_count_t monad_get_ticks_count(std::memory_order rel)
{
    return get_ticks_count(rel);
}

extern "C" monad_cpu_ticks_count_t monad_ticks_per_second()
{
    static monad_cpu_ticks_count_t v;
    if (v != 0) {
        return v;
    }
    std::array<double, 10> results;
    for (auto &result : results) {
        auto count1a = get_ticks_count(std::memory_order_acq_rel);
        auto ts1 = std::chrono::high_resolution_clock::now();
        auto count1b = get_ticks_count(std::memory_order_acq_rel);
        while (std::chrono::high_resolution_clock::now() - ts1 <
               std::chrono::milliseconds(100)) {
        }
        auto count2a = get_ticks_count(std::memory_order_acq_rel);
        auto ts2 = std::chrono::high_resolution_clock::now();
        auto count2b = get_ticks_count(std::memory_order_acq_rel);
        result = (double)(count2a + count2b - count1a - count1b) / 2.0 /
                 ((double)std::chrono::duration_cast<std::chrono::nanoseconds>(
                      ts2 - ts1)
                      .count() /
                  1000000000.0);
    }
    std::sort(results.begin(), results.end());
    v = (monad_cpu_ticks_count_t)((results[4] + results[5]) / 2);
    return v;
}
