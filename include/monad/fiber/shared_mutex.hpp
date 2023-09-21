#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>

#include <chrono>
#include <shared_mutex>

#include <boost/fiber/condition_variable.hpp>

MONAD_NAMESPACE_BEGIN

/// A shared mutex type derived from the standard library, but implemented in
/// terms of Boost.Fiber synchronization primitives. Wherever the original
/// implementation blocks, this implementation should yield.
class shared_mutex
{
    boost::fibers::mutex mutex_;
    boost::fibers::condition_variable gate1_;
    boost::fibers::condition_variable gate2_;
    uint32_t state_;

    static constexpr uint32_t WRITE_ENTERED = 1U << (sizeof(uint32_t) * 8 - 1);
    static_assert(WRITE_ENTERED == 0b10000000000000000000000000000000);

    static constexpr uint32_t MAX_READERS = ~WRITE_ENTERED;
    static_assert(MAX_READERS == 0b01111111111111111111111111111111);

    [[nodiscard]] bool write_entered() const { return state_ & WRITE_ENTERED; }

    [[nodiscard]] uint32_t readers() const { return state_ & MAX_READERS; }

public:
    shared_mutex()
        : state_{0}
    {
    }

    ~shared_mutex() { MONAD_ASSERT(state_ == 0); }

    shared_mutex(shared_mutex const &) = delete;
    shared_mutex &operator=(shared_mutex const &) = delete;

    // Exclusive ownership

    void lock()
    {
        std::unique_lock<boost::fibers::mutex> lock{mutex_};
        gate1_.wait(lock, [this] { return !write_entered(); });
        state_ |= WRITE_ENTERED;
        gate2_.wait(lock, [this] { return readers() == 0; });
    }

    [[nodiscard]] bool try_lock()
    {
        std::unique_lock<boost::fibers::mutex> lock(mutex_, std::try_to_lock);
        if (lock.owns_lock() && state_ == 0) {
            state_ = WRITE_ENTERED;
            return true;
        }
        return false;
    }
    void unlock()
    {
        std::lock_guard<boost::fibers::mutex> guard(mutex_);
        MONAD_ASSERT(write_entered());
        state_ = 0;
        gate1_.notify_all();
    }

    // Shared ownership

    void lock_shared()
    {
        std::unique_lock<boost::fibers::mutex> lock(mutex_);
        gate1_.wait(lock, [this] { return state_ < MAX_READERS; });
        ++state_;
    }

    [[nodiscard]] bool try_lock_shared()
    {
        std::unique_lock<boost::fibers::mutex> lock(mutex_, std::try_to_lock);

        if (!lock.owns_lock()) {
            return false;
        }
        if (state_ < MAX_READERS) {
            ++state_;
            return true;
        }
        return false;
    }

    void unlock_shared()
    {
        std::lock_guard<boost::fibers::mutex> guard(mutex_);
        MONAD_ASSERT(readers() > 0);
        auto prev = state_--;
        if (write_entered()) {
            if (readers() == 0) {
                gate2_.notify_one();
            }
        }
        else {
            if (prev == MAX_READERS) {
                gate1_.notify_one();
            }
        }
    }
};

MONAD_NAMESPACE_END
