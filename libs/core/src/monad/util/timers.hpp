#pragma once

#include <monad/config.hpp>

#include <atomic>
#include <chrono>
#include <map>
#include <thread>

MONAD_NAMESPACE_BEGIN

struct Timer
{
    std::atomic<uint64_t> evmone_total_time;
    std::atomic<uint64_t> evmone_reexec_total_time;
    std::atomic<uint64_t> evmone_keccak_time;
    std::atomic<uint64_t> evmone_reexec_keccak_time;
};

struct Timers final
{
    std::map<std::thread::id, Timer> timers{};
    Timer& get_timer();
};

MONAD_NAMESPACE_END
