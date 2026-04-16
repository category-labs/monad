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

#include <category/execution/ethereum/block_hash_buffer.hpp>

#include <array>

namespace monad::test
{
    class TestBlockHashBuffer : public BlockHashBuffer
    {
        using BlockHashBuffer::N;

        uint64_t block_number_;
        std::array<bytes32_t, N> blockhashes_;

    public:
        TestBlockHashBuffer()
            : block_number_{}
            , blockhashes_{}
        {
        }

        void set_block_number(uint64_t const block_number)
        {
            block_number_ = block_number;
        }

        uint64_t n() const override
        {
            return block_number_;
        }

        bytes32_t const &get(uint64_t const n) const override
        {
            MONAD_ASSERT_PRINTF(
                n < block_number_ && n + N >= block_number_,
                "n_=%lu, n=%lu",
                block_number_,
                n);
            auto const i = block_number_ - n;
            // n < block_number_ <= n + N  implies
            // 0 < block_number_ - n <= N  implies
            // 0 < i <= N  implies
            // N > N - i >= 0
            return blockhashes_.at(N - i);
        }
    };
}
