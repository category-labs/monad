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

#include <zkvm/guest/witness_block_hash_buffer.hpp>

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

WitnessBlockHashBuffer::WitnessBlockHashBuffer()
    : b_{}
    , first_{0}
    , n_{0}
{
}

uint64_t WitnessBlockHashBuffer::n() const
{
    return n_;
}

bytes32_t const &WitnessBlockHashBuffer::get(uint64_t const n) const
{
    // The run [first_, n_) is contiguous (enforced by set), so a number is
    // readable iff it lies in that run and within the ring's reach.
    MONAD_ASSERT_PRINTF(
        n >= first_ && n < n_ && n + N >= n_,
        "block hash %lu not in witness (first_=%lu, n_=%lu)",
        n,
        first_,
        n_);
    return b_[n % N];
}

void WitnessBlockHashBuffer::set(uint64_t const n, bytes32_t const &h)
{
    MONAD_ASSERT_PRINTF(!n_ || n == n_, "n_=%lu, n=%lu", n_, n);
    if (!n_) {
        first_ = n;
    }
    b_[n % N] = h;
    n_ = n + 1;
}

MONAD_NAMESPACE_END
