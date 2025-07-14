#include "gtest/gtest.h"
#include <category/async/detail/scope_polyfill.hpp>

#include <atomic>
#include <monad/mpt/detail/db_metadata.hpp>

#include <chrono>
#include <stop_token>
#include <thread>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

TEST(db_metadata, DISABLED_copy)
{
#if MONAD_CONTEXT_HAVE_TSAN
    return; // This test explicitly relies on racy memory copying
#endif
    monad::mpt::detail::db_metadata *metadata[3];
    metadata[0] = (monad::mpt::detail::db_metadata *)calloc(
        1, sizeof(monad::mpt::detail::db_metadata));
    metadata[1] = (monad::mpt::detail::db_metadata *)calloc(
        1, sizeof(monad::mpt::detail::db_metadata));
    metadata[2] = (monad::mpt::detail::db_metadata *)calloc(
        1, sizeof(monad::mpt::detail::db_metadata));
    auto unmetadata = monad::make_scope_exit([&]() noexcept {
        free(metadata[0]);
        free(metadata[1]);
        free(metadata[2]);
    });
    std::atomic<int> latch{-1};
    std::jthread thread([&](std::stop_token tok) {
        while (!tok.stop_requested()) {
            int expected = 0;
            while (!latch.compare_exchange_strong(
                       expected, 1, std::memory_order_acq_rel) &&
                   !tok.stop_requested()) {
                std::this_thread::yield();
                expected = 0;
            }
            db_copy(
                metadata[0],
                metadata[1],
                sizeof(monad::mpt::detail::db_metadata));
            MONAD_ASSERT(
                !metadata[0]->is_dirty().load(std::memory_order_acquire));
            latch.store(-1, std::memory_order_release);
        }
    });
    metadata[1]->chunk_info_count = 6;
    metadata[1]->capacity_in_free_list = 6;
    unsigned count = 0;
    auto const begin = std::chrono::steady_clock::now();
    while (std::chrono::steady_clock::now() - begin <
           std::chrono::seconds((count == 0) ? 60 : 5)) {
        if (metadata[0]->is_dirty().load(std::memory_order_acquire)) {
            EXPECT_FALSE(true);
        }
        metadata[0]->chunk_info_count = 5;
        metadata[0]->capacity_in_free_list = 5;
        latch.store(0, std::memory_order_release);
        do {
            memcpy((void *)metadata[2], metadata[0], 32);
            // If first half copied but not yet second half, dirty bit must be
            // set
            if (metadata[2]->chunk_info_count != 5 &&
                metadata[2]->capacity_in_free_list == 5) {
                if (!metadata[2]->is_dirty().load(std::memory_order_acquire)) {
                    EXPECT_TRUE(metadata[2]->is_dirty().load(
                        std::memory_order_acquire));
                }
                count++;
            }
        }
        while (latch.load(std::memory_order_acquire) != -1);
    }
    thread.request_stop();
    thread.join();
    EXPECT_GT(count, 0);
    std::cout << count << std::endl;
}
