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
#include <category/execution/ethereum/block_hash_buffer.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

//! BLOCKHASH source for the guest, filled from the witness's ancestor
//! headers. Only block numbers that were actually set are readable: a `get`
//! outside the run of set headers aborts, where BlockHashBufferFinalized
//! would hand back the zero hash sitting in a never-written slot.
class WitnessBlockHashBuffer : public BlockHashBuffer
{
    bytes32_t b_[N];
    uint64_t first_; // lowest block number set
    uint64_t n_; // one past the highest block number set; 0 while empty

public:
    WitnessBlockHashBuffer();

    uint64_t n() const override;
    bytes32_t const &get(uint64_t) const override;

    //! Block numbers must arrive in ascending order without gaps.
    void set(uint64_t, bytes32_t const &);
};

MONAD_NAMESPACE_END
