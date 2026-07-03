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
#include <category/mpt/config.hpp>
#include <category/vm/vm.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_MPT_NAMESPACE_BEGIN
class Db;
MONAD_MPT_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

struct Chain;
struct Db;
class TrieDb;
class BlockHashBufferFinalized;

namespace fiber
{
    class PriorityPool;
}

/// When set, every executed block also emits a zkVM execution witness to
/// `dir/<block>.witness` and the post-state root to
/// `dir/<block>.post_state_root`. Witness generation walks the live mpt
/// pre-commit, so it needs the raw db and the TrieDb wrapper, not just the
/// abstract Db interface the runloop executes against.
struct WitnessDumpConfig
{
    mpt::Db &raw_db;
    TrieDb &triedb;
    std::filesystem::path dir;
};

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &, std::filesystem::path const &, Db &, vm::VM &,
    BlockHashBufferFinalized &, fiber::PriorityPool &, uint64_t &, uint64_t,
    sig_atomic_t const volatile &, bool enable_tracing,
    std::filesystem::path const &rlp_path = {},
    WitnessDumpConfig const *witness_dump = nullptr);

MONAD_NAMESPACE_END
