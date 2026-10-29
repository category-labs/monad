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
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/util.hpp>
#include <category/vm/code.hpp>

#include <cstdint>
#include <functional>
#include <optional>

MONAD_NAMESPACE_BEGIN

// State backend for running the rpc executor without an on-disk database,
// e.g. in tests. It models an empty world: every account is absent, so a
// request only observes the state supplied by its state overrides. Operations
// that require real chain data (block headers, roots, non-empty code) or that
// would write to the database throw `MonadException`.
class NullDb final : public Db
{
    uint64_t block_number_{mpt::INVALID_BLOCK_NUM};

public:
    bool is_page_encoded() const override;

    std::optional<Account> read_account(Address const &) override;

    bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &) override;

    storage_page_t
    read_storage_page(Address const &, Incarnation, bytes32_t const &) override;

    vm::SharedIntercode read_code(bytes32_t const &) override;

    BlockHeader read_eth_header() override;
    bytes32_t state_root() override;
    bytes32_t receipts_root() override;
    bytes32_t transactions_root() override;
    std::optional<bytes32_t> withdrawals_root() override;

    void set_block_and_prefix(
        uint64_t block_number,
        bytes32_t const &block_id = bytes32_t{}) override;
    void finalize(uint64_t, bytes32_t const &) override;
    void update_verified_block(uint64_t) override;
    void update_voted_metadata(uint64_t, bytes32_t const &) override;
    void update_proposed_metadata(uint64_t, bytes32_t const &) override;

    uint64_t get_block_number() const override;

    void commit(
        bytes32_t const &, CommitBuilder &, BlockHeader const &,
        StateDeltas const &, std::function<void(BlockHeader &)>) override;
};

MONAD_NAMESPACE_END
