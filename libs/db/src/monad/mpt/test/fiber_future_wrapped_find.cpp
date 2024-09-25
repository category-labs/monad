#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include "fuzz/one_hundred_updates.hpp"

#include <monad/async/config.hpp>
#include <monad/async/io.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/c_result.h>
#include <monad/core/hex_literal.hpp>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_semaphore.h>
#include <monad/fiber/run_queue.h>
#include <monad/mpt/trie.hpp>
#include <monad/mpt/update.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <bit>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <deque>
#include <thread>
#include <utility>
#include <vector>

namespace
{
    using namespace monad::test;
    using namespace MONAD_ASYNC_NAMESPACE;

    struct FindArgs
    {
        UpdateAuxImpl *aux;
        inflight_map_t *const inflights;
        Node *const root;
        monad::byte_string_view const key;
        monad::byte_string_view const value;
    };

    monad_c_result find(monad_fiber_args_t mfa)
    {
        DbSyncObject sync;
        find_cursor_result_type result;

        auto *const find_args = std::bit_cast<FindArgs *>(mfa.arg[0]);
        fiber_find_request_t const request{
            .sync = &sync,
            .result = &result,
            .start = NodeCursor{*find_args->root},
            .key = find_args->key};
        find_notify_fiber_future(
            *find_args->aux, *find_args->inflights, request);
        sync.acquire();
        auto const [it, errc] = result;
        if (!it.is_valid()) {
            // TODO(ken): make this return a code in the real domain
            return monad_c_make_failure(EINVAL);
        }
        EXPECT_EQ(errc, monad::mpt::find_result::success);
        EXPECT_EQ(it.node->value(), find_args->value);
        return monad_c_make_success(0);
    }

    void init_find_fiber(
        monad_fiber_t **fiber, monad_fiber_prio_t prio, FindArgs *find_args)
    {
        ASSERT_EQ(0, monad_fiber_create(nullptr, fiber));
        ASSERT_EQ(
            0,
            monad_fiber_set_function(
                *fiber, prio, find, {std::bit_cast<uintptr_t>(find_args)}));
    }

    TEST_F(OnDiskMerkleTrieGTest, single_thread_one_find_fiber)
    {
        std::vector<Update> updates;
        for (auto const &i : one_hundred_updates) {
            updates.emplace_back(make_update(i.first, i.second));
        }
        this->root = upsert_vector(
            this->aux, *this->sm, std::move(this->root), std::move(updates));
        EXPECT_EQ(
            root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_hex);

        inflight_map_t inflights;
        FindArgs find_args = {
            &this->aux,
            &inflights,
            root.get(),
            one_hundred_updates[0].first,
            one_hundred_updates[0].second};

        monad_fiber_t *fiber;
        monad_fiber_suspend_info_t suspend_info;
        init_find_fiber(&fiber, MONAD_FIBER_PRIO_HIGHEST, &find_args);

        while (true) {
            int const rc = monad_fiber_run(fiber, &suspend_info);
            ASSERT_EQ(rc, 0);
            if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
                ASSERT_TRUE(MONAD_OK(suspend_info.eval));
                ASSERT_EQ(suspend_info.eval.value, 0);
                break;
            }
            do {
                aux.io->poll_nonblocking(1);
                std::this_thread::sleep_for(std::chrono::milliseconds(1));
            }
            while (!monad_fiber_is_runnable(fiber));
        }
        monad_fiber_destroy(fiber);
    }

    TEST_F(OnDiskMerkleTrieGTest, single_thread_one_hundred_find_fibers)
    {
        std::vector<Update> updates;
        for (auto const &i : one_hundred_updates) {
            updates.emplace_back(make_update(i.first, i.second));
        }
        this->root = upsert_vector(
            this->aux, *this->sm, std::move(this->root), std::move(updates));
        EXPECT_EQ(
            root_hash(),
            0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_hex);

        inflight_map_t inflights;
        std::vector<monad_fiber_t *> fibers;
        std::deque<FindArgs> fiber_func_args;
        monad_run_queue_t *run_queue;

        ASSERT_EQ(
            0,
            monad_run_queue_create(
                nullptr, size(one_hundred_updates), &run_queue));
        for (std::size_t i = 0; auto const &[key, val] : one_hundred_updates) {
            FindArgs &find_args = fiber_func_args.emplace_back(
                &this->aux, &inflights, root.get(), key, val);
            monad_fiber_t *&fiber = fibers.emplace_back();
            auto const update_priority =
                MONAD_FIBER_PRIO_HIGHEST + static_cast<monad_fiber_prio_t>(i++);
            init_find_fiber(&fiber, update_priority, &find_args);
            ASSERT_EQ(0, monad_run_queue_try_push(run_queue, fiber));
        }

        std::size_t fibers_done = 0;
        while (fibers_done < size(one_hundred_updates)) {
            monad_fiber_suspend_info_t suspend_info;
            monad_fiber_t *next_fiber = monad_run_queue_try_pop(run_queue);

            while (next_fiber == nullptr) {
                // When there's nothing to do, I/O poll until at least one fiber
                // is scheduled to run again
                aux.io->poll_nonblocking(1);
                std::this_thread::sleep_for(std::chrono::milliseconds(1));
                next_fiber = monad_run_queue_try_pop(run_queue);
            }

            int const rc = monad_fiber_run(next_fiber, &suspend_info);
            ASSERT_EQ(rc, 0);
            if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
                ASSERT_TRUE(MONAD_OK(suspend_info.eval));
                ASSERT_EQ(suspend_info.eval.value, 0);
                ++fibers_done;
            }
        }

        ASSERT_TRUE(monad_run_queue_is_empty(run_queue));
        for (monad_fiber_t *fiber : fibers) {
            monad_fiber_destroy(fiber);
        }
        monad_run_queue_destroy(run_queue);
    }
}
