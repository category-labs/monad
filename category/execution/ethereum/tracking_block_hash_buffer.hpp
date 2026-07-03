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
#include <optional>

MONAD_NAMESPACE_BEGIN

/// Records the minimum block number queried via BLOCKHASH during execution.
class TrackingBlockHashBuffer final : public BlockHashBuffer
{
    BlockHashBuffer const &inner_;
    mutable std::optional<uint64_t> min_queried_;

public:
    explicit TrackingBlockHashBuffer(BlockHashBuffer const &inner)
        : inner_{inner}
    {
    }

    uint64_t n() const override
    {
        return inner_.n();
    }

    bytes32_t const &get(uint64_t const block_number) const override
    {
        if (!min_queried_ || block_number < *min_queried_) {
            min_queried_ = block_number;
        }
        return inner_.get(block_number);
    }

    std::optional<uint64_t> min_queried() const
    {
        return min_queried_;
    }
};

MONAD_NAMESPACE_END
