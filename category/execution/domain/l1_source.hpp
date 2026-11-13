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

#include <category/core/address.hpp>
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

// Where monad-domain reads the finalized L1 chain from.
class L1Source
{
public:
    virtual ~L1Source() = default;

    // The latest finalized L1 block, or mpt::INVALID_BLOCK_NUM before the
    // first.
    virtual uint64_t latest_finalized() const = 0;

    // The header of finalized L1 block `number`. Fails with
    // mpt::DbError::version_no_longer_exist while `number` is past
    // latest_finalized() or once the block has left the source's history.
    virtual Result<BlockHeader>
    read_finalized_header(uint64_t number) const = 0;

    // The receipts of finalized L1 block `number`, in transaction order.
    // Fails like read_finalized_header.
    virtual Result<std::vector<Receipt>>
    read_finalized_receipts(uint64_t number) const = 0;

    // The earliest L1 block the source still has.
    virtual uint64_t earliest() const = 0;

    // Storage slot `slot` of `address` as of finalized L1 block `number`:
    // zero if the account or the slot is absent. Fails like
    // read_finalized_header.
    virtual Result<bytes32_t> read_storage(
        uint64_t number, Address const &address,
        bytes32_t const &slot) const = 0;
};

// Reads the finalized chain from an L1 node's triedb, which may be open
// read-only while the node writes it.
class TrieDbL1Source final : public L1Source
{
    mpt::Db &db_;

public:
    explicit TrieDbL1Source(mpt::Db &);

    uint64_t latest_finalized() const override;
    Result<BlockHeader> read_finalized_header(uint64_t number) const override;
    Result<std::vector<Receipt>>
    read_finalized_receipts(uint64_t number) const override;
    uint64_t earliest() const override;
    Result<bytes32_t> read_storage(
        uint64_t number, Address const &address,
        bytes32_t const &slot) const override;
};

MONAD_DOMAIN_NAMESPACE_END
