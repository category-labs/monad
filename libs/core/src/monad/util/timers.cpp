#include <mutex>

#include <monad/util/timers.hpp>
#include <monad/core/likely.h>

MONAD_NAMESPACE_BEGIN

std::mutex timers_mutex;

Timer& Timers::get_timer()
{
    auto tid = std::this_thread::get_id();
    auto it = timers.find(tid); 
    if (MONAD_UNLIKELY(it == timers.end())) {
        std::lock_guard<std::mutex> guard(timers_mutex);
        auto [it2,_] = timers.try_emplace(tid);
        return it2->second;
    }
    else return it->second;
};

MONAD_NAMESPACE_END