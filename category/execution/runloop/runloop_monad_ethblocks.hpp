// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/vm/vm.hpp>

#include <chrono>
#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

struct MonadChain;
struct Db;
class BlockHashBufferFinalized;
class ExecutionEventRecorder;

namespace fiber
{
    class PriorityPool;
}

// Blocks always execute on and commit to the primary `db`, whose encoding
// must match the block's revision. A page-encoded `secondary_db`, when
// non-null, is the pre-promote migration backfill and is mirrored on every
// commit; a slot-encoded secondary is post-promote frozen history and takes no
// writes.
Result<std::pair<uint64_t, uint64_t>> runloop_monad_ethblocks(
    MonadChain const &, std::filesystem::path const &, Db &, Db *secondary_db,
    vm::VM &, BlockHashBufferFinalized &, fiber::PriorityPool &, uint64_t &,
    uint64_t, sig_atomic_t const volatile &, bool enable_tracing,
    std::chrono::seconds block_db_timeout, ExecutionEventRecorder *);

MONAD_NAMESPACE_END
