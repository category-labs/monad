// Copyright (C) 2025 Category Labs, Inc.
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
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/vm/evm/traits.hpp>

#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
struct CallFrame;
struct Receipt;
struct Transaction;
struct Withdrawal;
struct Db;

// Per-block ancillary inputs that the dual commit path forwards to the
// shared CommitBuilder helpers. Root state deltas are passed directly to
// commit_block so each builder can encode the same logical writes.
struct BlockCommitAncillaries
{
    Code const &code;
    std::vector<Receipt> const &receipts;
    std::vector<Transaction> const &transactions;
    std::vector<Address> const &senders;
    std::vector<std::vector<CallFrame>> const &call_frames;
    std::vector<BlockHeader> const &ommers;
    std::optional<std::vector<Withdrawal>> const &withdrawals;
};

struct PrivateDomainBlockCommitInput
{
    uint64_t domain_id;
    DomainStateDeltas const &state_deltas;
    Code const &code;
    std::span<Transaction const> transactions;
    std::span<std::optional<Address> const> senders;
    std::span<Receipt const> receipts;
};

template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_block(
    Db &primary_db, Db *secondary_db, bytes32_t const &block_id,
    BlockHeader const &header, StateDeltas const &state,
    BlockCommitAncillaries const &anc);

// apply f to both dbs that are present
template <typename F>
void for_each_db(Db &db, Db *const secondary_db, F &&f)
{
    f(db);
    if (secondary_db != nullptr) {
        f(*secondary_db);
    }
}

template <Traits traits>
    requires is_monad_trait_v<traits>
DomainStateRoots commit_private_domain_batch(
    Db &primary_db, Db *secondary_db, bytes32_t const &block_id,
    BlockHeader const &header,
    std::span<PrivateDomainBlockCommitInput const> blocks);

MONAD_NAMESPACE_END
