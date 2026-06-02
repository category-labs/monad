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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/mpt/db.hpp>
#include <category/rpc/eth_simulate_block_hash_buffer.hpp>
#include <category/rpc/lazy_block_hash.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

EthSimulateBlockHashBuffer::EthSimulateBlockHashBuffer(
    mpt::RODb const &db, uint64_t const n,
    std::optional<bytes32_t const> const &base_block_hash)
    : LazyBlockHash(db, n)
    , n_{n}
    , i_{0}
    , base_block_hash_{base_block_hash}
    , simulated_block_hashes_{}
{
}

uint64_t EthSimulateBlockHashBuffer::n() const
{
    return n_ + i_;
}

bytes32_t const &EthSimulateBlockHashBuffer::get(uint64_t const n) const
{
    uint64_t const current_n = this->n();
    MONAD_ASSERT_PRINTF(
        n < current_n && n + N >= current_n, "n_=%lu, n=%lu", current_n, n);

    // Simulated blocks begin at `n_`. Querying a block number at or
    // above `n_` means we should read from the simulated-hash window.
    if (n >= n_) {
        size_t const idx = static_cast<size_t>(n - n_);
        MONAD_ASSERT_PRINTF(
            idx < i_,
            "missing simulated block hash: n=%lu, idx=%zu, i_=%lu",
            n,
            idx,
            i_);
        return simulated_block_hashes_[idx];
    }

    // If we are querying the base block, then we need to take care, as
    // the base block may not have been finalized yet, meaning a call to
    // `LazyBlockHash::get(n)` would throw (since it only reads
    // finalized blocks). Therefore we special case this query to return
    // the provided base block hash.
    if (n + 1 == n_ && base_block_hash_.has_value()) {
        return *base_block_hash_;
    }

    return LazyBlockHash::get(n);
}

void EthSimulateBlockHashBuffer::advance(bytes32_t const &simulated_block_hash)
{
    MONAD_ASSERT_PRINTF(
        i_ < N, "block hash buffer overflow: i_=%lu, N=%u", i_, N);
    simulated_block_hashes_[i_++] = simulated_block_hash;
}

MONAD_NAMESPACE_END
