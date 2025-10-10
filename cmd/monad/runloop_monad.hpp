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
#include <category/vm/vm.hpp>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

struct MonadChain;
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

Result<std::pair<uint64_t, uint64_t>> runloop_monad_live(
    MonadChain const &, std::filesystem::path const &, mpt::Db &, Db &,
    vm::VM &, BlockHashBufferFinalized &, fiber::PriorityPool &,
    uint64_t &output_block_num, uint64_t end_block_num,
    sig_atomic_t const volatile &stop, bool enable_tracing);

Result<std::pair<uint64_t, uint64_t>> runloop_monad_replay(
    MonadChain const &, std::filesystem::path const &, mpt::Db &, Db &,
    vm::VM &, BlockHashBufferFinalized &, fiber::PriorityPool &,
    uint64_t &output_block_num, uint64_t const end_block_num,
    sig_atomic_t const volatile &stop, bool enable_tracing);

MONAD_NAMESPACE_END
