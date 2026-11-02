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

#include <category/core/config.hpp>
#include <category/execution/ethereum/db/db.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// One private domain's state as a Db, so that State and BlockState execute
// against it unchanged. Its state reads go to the domain's own tries through
// the wrapped Db, at whatever block that Db is set to; nothing is cached.
// Nothing is written through it: a domain block's state is committed with the
// L1 block it was derived from. The L1's headers, roots and block cursor are
// not the domain's, and reading or moving them aborts.
// See docs/domains-protocol.md.
class DomainDb final : public Db
{
    Db &db_;
    uint64_t const domain_chain_id_;

public:
    DomainDb(Db &, uint64_t domain_chain_id);

    uint64_t domain_chain_id() const
    {
        return domain_chain_id_;
    }

    bool is_page_encoded() const override;
    std::optional<Account> read_account(Address const &) override;
    bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;
    storage_page_t read_storage_page(
        Address const &, Incarnation, bytes32_t const &page_key) override;
    vm::SharedIntercode read_code(bytes32_t const &) override;
    bytes32_t state_root() override;
    uint64_t get_block_number() const override;

    BlockHeader read_eth_header() override;
    bytes32_t receipts_root() override;
    bytes32_t transactions_root() override;
    std::optional<bytes32_t> withdrawals_root() override;
    void set_block_and_prefix(
        uint64_t block_number, bytes32_t const &block_id) override;
    void finalize(uint64_t block_number, bytes32_t const &block_id) override;
    void update_verified_block(uint64_t block_number) override;
    void update_voted_metadata(
        uint64_t block_number, bytes32_t const &block_id) override;
    void update_proposed_metadata(
        uint64_t block_number, bytes32_t const &block_id) override;
    void commit(
        bytes32_t const &block_id, CommitBuilder &, BlockHeader const &,
        StateDeltas const &,
        std::function<void(BlockHeader &)> populate_header_fn) override;
};

MONAD_NAMESPACE_END
