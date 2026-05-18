// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/core/lru/static_lru_cache.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/mpt/db.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// eth call on latest uses eip-2935. historical eth calls use this class,
// which lazily loads the block header from the DB and computes BLOCKHASH.
// historical can always query from the finalized prefix.
//
// A thread-safe LRU is not needed. Each submitted call to the executor pool
// creates its own LazyBlockHash instance.
class LazyBlockHash : public BlockHashBuffer
{
    using BlockHashBuffer::N;

    mpt::RODb const &db_;
    uint64_t const n_;
    using Cache = static_lru_cache<uint64_t, bytes32_t>;
    mutable Cache blockhash_cache_;

public:
    LazyBlockHash(mpt::RODb const &db, uint64_t const n);
    ~LazyBlockHash() override = default;

    uint64_t n() const override;
    bytes32_t const &get(uint64_t const n) const override;
};

MONAD_NAMESPACE_END
