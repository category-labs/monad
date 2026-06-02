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
#include <category/mpt/db.hpp>
#include <category/rpc/lazy_block_hash.hpp>

#include <array>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

// The `eth_simulateV1` method needs to be able to read hashes of both
// finalized and simulated blocks. This buffer piggybacks on lazy block hash
// buffer for finalized blocks, while providing a method for appending the
// block hashes of simulated blocks such that they can be read by later
// simulated blocks.
class EthSimulateBlockHashBuffer : public LazyBlockHash
{
    using LazyBlockHash::N;

    uint64_t const n_;
    uint64_t i_;
    std::optional<bytes32_t const> const base_block_hash_;
    std::array<bytes32_t, N> simulated_block_hashes_;

public:
    EthSimulateBlockHashBuffer(
        mpt::RODb const &db, uint64_t const n,
        std::optional<bytes32_t const> const &base_block_hash);

    ~EthSimulateBlockHashBuffer() override = default;

    uint64_t n() const override;

    bytes32_t const &get(uint64_t const) const override;

    void advance(bytes32_t const &);
};

MONAD_NAMESPACE_END
