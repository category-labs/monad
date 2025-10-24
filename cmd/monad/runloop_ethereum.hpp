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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <filesystem>
#include <utility>

#include <signal.h>

MONAD_NAMESPACE_BEGIN

struct Block;
struct BlockHeader;
class BlockHashBuffer;
struct Chain;
struct Db;
class BlockHashBufferFinalized;

namespace fiber
{
    class PriorityPool;
}

struct BlockCacheEntry
{
    uint64_t block_number;
    bytes32_t parent_id;
    ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;
};

using BlockCache =
    ankerl::unordered_dense::segmented_map<bytes32_t, BlockCacheEntry>;

template <Traits traits>
Result<BlockHeader> process_ethereum_block(
    Chain const &chain, Db &db, vm::VM &vm,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool, Block const &block,
    bytes32_t const &block_id, bytes32_t const &parent_block_id,
    bool const enable_tracing, BlockCache * = nullptr);

Result<std::pair<uint64_t, uint64_t>> runloop_ethereum(
    Chain const &, std::filesystem::path const &, Db &, vm::VM &,
    BlockHashBufferFinalized &, fiber::PriorityPool &, uint64_t &, uint64_t,
    sig_atomic_t const volatile &, bool enable_tracing);

MONAD_NAMESPACE_END
