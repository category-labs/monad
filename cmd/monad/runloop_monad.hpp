#pragma once

#include <monad/config.hpp>
#include <monad/core/result.hpp>

#include <atomic>
#include <cstdint>
#include <filesystem>
#include <utility>

MONAD_NAMESPACE_BEGIN

struct Chain;
struct Db;
class BlockHashBufferFinalized;

namespace mpt
{
    class Db;
}

namespace fiber
{
    class PriorityPool;
}

Result<std::pair<uint64_t, uint64_t>> runloop_monad(
    Chain const &, std::filesystem::path const &, mpt::Db &, Db &,
    BlockHashBufferFinalized &, fiber::PriorityPool &, uint64_t &, uint64_t,
    std::atomic<bool> const &);

MONAD_NAMESPACE_END
