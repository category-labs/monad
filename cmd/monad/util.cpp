#include "util.hpp"

#include <monad/procfs/statm.h>

#include <quill/Quill.h>
#include <quill/detail/LogMacros.h>

#include <algorithm>
#include <chrono>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-variable"
#pragma GCC diagnostic ignored "-Wunused-parameter"

void log_tps(
    uint64_t const block_num, uint64_t const nblocks, uint64_t const ntxs,
    uint64_t const gas, std::chrono::steady_clock::time_point const begin)
{
    auto const now = std::chrono::steady_clock::now();
    auto const elapsed = std::max(
        static_cast<uint64_t>(
            std::chrono::duration_cast<std::chrono::microseconds>(now - begin)
                .count()),
        1UL); // for the unlikely case that elapsed < 1 mic
    uint64_t const tps = (ntxs) * 1'000'000 / elapsed;
    uint64_t const gps = gas / elapsed;

    LOG_INFO(
        "Run {:4d} blocks to {:8d}, number of transactions {:6d}, "
        "tps = {:5d}, gps = {:4d} M, rss = {:6d} MB",
        nblocks,
        block_num,
        ntxs,
        tps,
        gps,
        monad_procfs_self_resident() / (1L << 20));
};

#pragma GCC diagnostic pop

MONAD_NAMESPACE_END
