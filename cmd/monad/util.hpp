#pragma once

#include <monad/config.hpp>

#include <chrono>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

void log_tps(
    uint64_t const block_num, uint64_t const nblocks, uint64_t const ntxs,
    uint64_t const gas, std::chrono::steady_clock::time_point const begin);

MONAD_NAMESPACE_END
