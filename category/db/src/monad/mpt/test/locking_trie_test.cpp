#define BOOST_THREAD_VERSION 3 // must go before all else

#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp" // NOLINT

#include <monad/mpt/trie.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <boost/thread/pthread/shared_mutex.hpp>

#include <cstdint>
#include <mutex>
#include <ostream>
#include <sstream>
#include <vector>

struct TestMutex
{
    struct event_t
    {
        enum type_t : uint8_t
        {
            unknown,
            lock,
            unlock,
            lock_shared,
            unlock_shared,
            try_unlock_shared_and_lock_success,
            try_unlock_shared_and_lock_failure,
            unlock_and_lock_shared
        } type;
    };

    std::mutex lock_;
    std::vector<event_t> events;

    ::boost::shared_mutex mutex;

    void clear()
    {
        events.clear();
    }

    std::ostream &dump(std::ostream &s)
    {
        for (auto &ev : events) {
            s << "   ";
            switch (ev.type) {
            case event_t::unknown:
                s << "unknown";
                break;
            case event_t::lock:
                s << "lock exclusive";
                break;
            case event_t::unlock:
                s << "unlock exclusive";
                break;
            case event_t::lock_shared:
                s << "lock shared";
                break;
            case event_t::unlock_shared:
                s << "unlock shared";
                break;
            case event_t::try_unlock_shared_and_lock_success:
                s << "upgrade shared to exclusive success";
                break;
            case event_t::try_unlock_shared_and_lock_failure:
                s << "upgrade shared to exclusive failure";
                break;
            case event_t::unlock_and_lock_shared:
                s << "downgrade exclusive to shared";
                break;
            }
            s << "\n";
        }
        return s;
    }

public:
    void lock()
    {
        mutex.lock();
        std::lock_guard const g(lock_);
        events.emplace_back(event_t::lock);
    }

    void unlock()
    {
        mutex.unlock();
        std::lock_guard const g(lock_);
        events.emplace_back(event_t::unlock);
    }

    void lock_shared()
    {
        mutex.lock_shared();
        std::lock_guard const g(lock_);
        events.emplace_back(event_t::lock_shared);
    }

    void unlock_shared()
    {
        mutex.unlock_shared();
        std::lock_guard const g(lock_);
        events.emplace_back(event_t::unlock_shared);
    }

    bool try_unlock_shared_and_lock()
    {
#ifdef BOOST_THREAD_PROVIDES_SHARED_MUTEX_UPWARDS_CONVERSIONS
        if (mutex.try_unlock_shared_and_lock()) {
            std::lock_guard const g(lock_);
            events.emplace_back(event_t::try_unlock_shared_and_lock_success);
            return true;
        }
#else
        if (mutex.try_lock_upgrade()) {
            if (mutex.try_unlock_upgrade_and_lock()) {
                std::lock_guard g(lock_);
                events.emplace_back(
                    event_t::try_unlock_shared_and_lock_success);
                return true;
            }
            mutex.unlock_upgrade_and_lock_shared();
        }
#endif
        std::lock_guard const g(lock_);
        events.emplace_back(event_t::try_unlock_shared_and_lock_failure);
        return false;
    }

    void unlock_and_lock_shared()
    {
        mutex.unlock_and_lock_shared();
        std::lock_guard const g(lock_);
        events.emplace_back(event_t::unlock_and_lock_shared);
    }
};

struct LockingTrieTest
    : public monad::test::FillDBWithChunksGTest<
          monad::test::FillDBWithChunksConfig{.chunks_to_fill = 2}, TestMutex>
{
};

TEST_F(LockingTrieTest, works)
{
    auto &aux = this->state()->aux;
    auto *root = this->state()->root.get();
    auto const version = aux.db_history_max_version();
    auto &keys = this->state()->keys;
    // Appending blocks only does exclusive lock and unlock and nothing else
    {
        std::stringstream ss;
        aux.lock().dump(ss);
        EXPECT_STREQ(ss.str().c_str(), R"(   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
   lock exclusive
   unlock exclusive
)");
    }

    // Finding a blocking item should share lock, upgrade to exclusive,
    // downgrade back to shared, release
    {
        aux.lock().clear();
        auto [leaf_it, res] =
            find_blocking(aux, *root, keys.back().first, version);
        EXPECT_EQ(res, monad::mpt::find_result::success);
        EXPECT_NE(leaf_it.node, nullptr);
        EXPECT_TRUE(leaf_it.node->has_value());

        std::stringstream ss;
        this->state()->aux.lock().dump(ss);
        EXPECT_STREQ(ss.str().c_str(), R"(   lock shared
   upgrade shared to exclusive success
   downgrade exclusive to shared
   unlock shared
)");
    }

    // Now the node is in cache, no exclusive lock should get taken
    {
        aux.lock().clear();
        auto [leaf_it, res] =
            find_blocking(aux, *root, keys.back().first, version);
        EXPECT_EQ(res, monad::mpt::find_result::success);
        EXPECT_NE(leaf_it.node, nullptr);
        EXPECT_TRUE(leaf_it.node->has_value());

        std::stringstream ss;
        this->state()->aux.lock().dump(ss);
        EXPECT_STREQ(ss.str().c_str(), R"(   lock shared
   unlock shared
)");
    }

#if 0 // will restore after IoWorkerPool upgrade (not this PR)

    /* Finding a non-blocking item should:
    1. Take a shared lock, if item is in cache, unlock and return.
    2. If item is not in cache, upgrade to an exclusive lock, initiate the i/o,
    release the lock.
    3. When the i/o completes, take an exclusive lock, update the cache,
    release.
    */
    {
        aux.lock().clear();
        ::boost::fibers::promise<::monad::mpt::find_result_type> p;
        auto fut = p.get_future();
        ::monad::mpt::inflight_map_t inflights;
        ::monad::mpt::find_request_t req{&p, *root, keys[keys.size() - 2].first};
        ::monad::mpt::find_notify_fiber_future(aux, inflights, req);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            aux.io->wait_until_done();
        }
        auto [leaf_it, res] = fut.get();
        EXPECT_EQ(res, monad::mpt::find_result::success);
        EXPECT_NE(leaf_it.node, nullptr);
        EXPECT_TRUE(leaf_it.node->has_value());

        std::stringstream ss;
        this->state()->aux.lock().dump(ss);
        EXPECT_STREQ(ss.str().c_str(), R"(   lock shared
   upgrade shared to exclusive success
   downgrade exclusive to shared
   unlock shared
   lock exclusive
   unlock exclusive
)");
    }

    // Now the node is in cache, no exclusive lock should get taken
    {
        aux.lock().clear();
        ::boost::fibers::promise<::monad::mpt::find_result_type> p;
        auto fut = p.get_future();
        ::monad::mpt::inflight_map_t inflights;
        ::monad::mpt::find_request_t req{&p, *root, keys[keys.size() - 2].first};
        ::monad::mpt::find_notify_fiber_future(aux, inflights, req);
        while (fut.wait_for(std::chrono::seconds(0)) !=
               ::boost::fibers::future_status::ready) {
            aux.io->wait_until_done();
        }
        auto [leaf_it, res] = fut.get();
        EXPECT_EQ(res, monad::mpt::find_result::success);
        EXPECT_NE(leaf_it.node, nullptr);
        EXPECT_TRUE(leaf_it.node->has_value());

        std::stringstream ss;
        this->state()->aux.lock().dump(ss);
        EXPECT_STREQ(ss.str().c_str(), R"(   lock shared
   unlock shared
)");
    }
#endif
}
