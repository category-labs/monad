#pragma once

#include <monad/core/assert.h>
#include <monad/fiber2/config.hpp>
#include <monad/fiber2/dispatcher.hpp>
#include <monad/fiber2/scheduler.hpp>

#include <boost/context/fiber.hpp>
#include <boost/fiber/detail/spinlock.hpp>

#include <mutex>
#include <utility>

MONAD_FIBER_NAMESPACE_BEGIN

class Future
{
    using Mutex = boost::fibers::detail::spinlock;
    using Lock = std::unique_lock<Mutex>;

    Mutex mutex_{};
    bool flag_{false};
    int64_t priority_{0};
    boost::context::fiber fiber_{};

public:
    void wait()
    {
        {
            Lock const lock{mutex_};
            if (flag_) {
                return;
            }
        }
        dispatcher_ = std::move(dispatcher_)
                          .resume_with([this](boost::context::fiber &&fiber) {
                              Lock const lock{mutex_};
                              if (!flag_) {
                                  priority_ = ::monad::fiber::priority_;
                                  fiber_ = std::move(fiber);
                                  return boost::context::fiber{};
                              }
                              return std::move(fiber);
                          });
    }

    void set_value()
    {
        Lock const lock{mutex_};
        MONAD_ASSERT(!flag_);
        flag_ = true;
        if (fiber_) {
            queue_.emplace(priority_, std::move(fiber_));
        }
    }
};

MONAD_FIBER_NAMESPACE_END
