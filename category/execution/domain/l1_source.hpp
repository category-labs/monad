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
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <category/mpt/util.hpp>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

MONAD_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

// An L1 block as private domain derivation reads it.
struct L1Block
{
    BlockHeader header;
    // keccak256(rlp(header)): the block's Ethereum block hash.
    bytes32_t hash;
    std::vector<Receipt> receipts;
};

// Where monad-domain reads the finalized L1 chain from.
class L1Source
{
public:
    virtual ~L1Source() = default;

    // The latest finalized L1 block, or mpt::INVALID_BLOCK_NUM before the
    // first.
    virtual uint64_t latest_finalized() const = 0;

    // Finalized L1 block `number`. Fails with
    // mpt::DbError::version_no_longer_exist while `number` is past
    // latest_finalized() or once the block has left the source's history.
    virtual Result<L1Block> read_finalized(uint64_t number) const = 0;
};

// Reads the finalized chain from an L1 node's triedb, which may be open
// read-only while the node writes it.
class TrieDbL1Source final : public L1Source
{
    mpt::Db &db_;

public:
    explicit TrieDbL1Source(mpt::Db &);

    uint64_t latest_finalized() const override;
    Result<L1Block> read_finalized(uint64_t number) const override;
};

MONAD_DOMAIN_NAMESPACE_END
