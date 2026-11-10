#pragma once

#include <monad/config.hpp>
#include <monad/core/result.hpp>
#include <monad/execution/block_hash_function.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

struct Chain;
struct Db;

namespace fiber
{
    class PriorityPool;
}

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &, std::filesystem::path const &, Db &,
    BlockHashFunction const &, fiber::PriorityPool &, uint64_t &, uint64_t,
    sig_atomic_t const volatile &);

MONAD_NAMESPACE_END
