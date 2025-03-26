#pragma once

#include <monad/config.hpp>

#include <quill/Quill.h>

#include <atomic>
#include <chrono>
#include <map>
#include <thread>

MONAD_NAMESPACE_BEGIN

struct Timer
{
    std::atomic<uint64_t> evmone_total_time;
    std::atomic<uint64_t> evmone_reexec_total_time;
};

struct Timers final
{
    std::map<std::thread::id, Timer> timers{};
    Timer& get_timer();
    void log_times()
    {
        for (auto it = timers.begin(); it != timers.end(); it++)
        {
            LOG_INFO("thread id {}: total evmone execution time = {}",
                    it->first, it->second.evmone_total_time);
            LOG_INFO("thread id {}: total evmone RE-execution time = {}",
                it->first, it->second.evmone_reexec_total_time);
        }
    }
};

MONAD_NAMESPACE_END