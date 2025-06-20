#pragma once

#include <monad/chain/chain_config.h>
#include <monad/config.hpp>
#include <monad/core/result.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

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
    monad_chain_config, std::filesystem::path const &, mpt::Db &, Db &,
    BlockHashBufferFinalized &, fiber::PriorityPool &, uint64_t &, uint64_t,
    sig_atomic_t const volatile &);

MONAD_NAMESPACE_END
