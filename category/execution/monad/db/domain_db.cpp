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

#include <category/core/assert.h>
#include <category/execution/monad/db/domain_db.hpp>
#include <category/execution/monad/db/storage_page.hpp>

MONAD_NAMESPACE_BEGIN

DomainDb::DomainDb(Db &db, uint64_t const domain_chain_id)
    : db_{db}
    , domain_chain_id_{domain_chain_id}
{
}

bool DomainDb::is_page_encoded() const
{
    return db_.is_page_encoded();
}

std::optional<Account> DomainDb::read_account(Address const &address)
{
    return db_.read_domain_account(domain_chain_id_, address);
}

bytes32_t DomainDb::read_storage(
    Address const &address, Incarnation, bytes32_t const &key)
{
    auto const page = db_.read_domain_storage(
        domain_chain_id_, address, storage_lookup_key(key));
    return page[is_page_encoded() ? compute_slot_offset(key) : 0];
}

storage_page_t DomainDb::read_storage_page(
    Address const &address, Incarnation, bytes32_t const &page_key)
{
    MONAD_ASSERT(is_page_encoded());
    return db_.read_domain_storage(domain_chain_id_, address, page_key);
}

vm::SharedIntercode DomainDb::read_code(bytes32_t const &code_hash)
{
    return db_.read_domain_code(domain_chain_id_, code_hash);
}

bytes32_t DomainDb::state_root()
{
    return db_.read_domain_state_root(domain_chain_id_);
}

uint64_t DomainDb::get_block_number() const
{
    return db_.get_block_number();
}

BlockHeader DomainDb::read_eth_header()
{
    MONAD_ABORT("a private domain has no L1 header");
}

bytes32_t DomainDb::receipts_root()
{
    MONAD_ABORT("a private domain's receipts root is not in the db");
}

bytes32_t DomainDb::transactions_root()
{
    MONAD_ABORT("a private domain's transactions root is not in the db");
}

std::optional<bytes32_t> DomainDb::withdrawals_root()
{
    MONAD_ABORT("a private domain has no withdrawals");
}

void DomainDb::set_block_and_prefix(uint64_t, bytes32_t const &)
{
    MONAD_ABORT("set the wrapped Db instead");
}

void DomainDb::finalize(uint64_t, bytes32_t const &)
{
    MONAD_ABORT("a private domain is finalized with the L1");
}

void DomainDb::update_verified_block(uint64_t)
{
    MONAD_ABORT("a private domain is verified with the L1");
}

void DomainDb::update_voted_metadata(uint64_t, bytes32_t const &)
{
    MONAD_ABORT("a private domain is voted on with the L1");
}

void DomainDb::update_proposed_metadata(uint64_t, bytes32_t const &)
{
    MONAD_ABORT("a private domain is proposed with the L1");
}

void DomainDb::commit(
    bytes32_t const &, CommitBuilder &, BlockHeader const &,
    StateDeltas const &, std::function<void(BlockHeader &)>)
{
    MONAD_ABORT("a private domain is committed with the L1 block");
}

MONAD_NAMESPACE_END
