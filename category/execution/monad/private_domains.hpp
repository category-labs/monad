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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/monad/private_domain_derivation.hpp>
#include <category/execution/monad/private_domain_hpke.hpp>

#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct Db;
struct Receipt;

// The private domains this node derives blocks for. With none, the node still
// writes the domain tables, for a db that has them.
struct PrivateDomains
{
    PrivateDomainKeyring keyring;
    // The L1 DomainHub contract.
    Address hub;
};

// The domain blocks derived from one L1 block, owning what their
// DomainBlockCommits view until the L1 block is committed.
class PrivateDomainBlocks
{
    std::vector<DerivedDomainBlock> blocks_;
    std::vector<byte_string> encoded_headers_;
    std::vector<DomainBlockCommit> commits_;
    bool derived_{false};

public:
    // On a node without private domains.
    PrivateDomainBlocks() = default;
    explicit PrivateDomainBlocks(std::vector<DerivedDomainBlock>);

    PrivateDomainBlocks(PrivateDomainBlocks const &) = delete;
    PrivateDomainBlocks &operator=(PrivateDomainBlocks const &) = delete;
    PrivateDomainBlocks(PrivateDomainBlocks &&) = default;
    PrivateDomainBlocks &operator=(PrivateDomainBlocks &&) = default;

    std::span<DerivedDomainBlock const> blocks() const
    {
        return blocks_;
    }

    // What commit_block writes to the domain tables: nullopt on a node
    // without private domains.
    std::optional<std::span<DomainBlockCommit const>> commits() const
    {
        if (!derived_) {
            return std::nullopt;
        }
        return commits_;
    }
};

// Derives the domain blocks of an executed L1 block. `parent_db` must be set
// to the L1 block's parent, where each domain's latest header is read.
// Returns an empty PrivateDomainBlocks without private domains.
Result<PrivateDomainBlocks> derive_private_domain_blocks(
    PrivateDomains const *, Db &parent_db, BlockHeader const &l1_header,
    bytes32_t const &l1_block_id, std::span<Receipt const> l1_receipts);

MONAD_NAMESPACE_END
