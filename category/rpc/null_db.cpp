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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/throw.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/rpc/null_db.hpp>
#include <category/vm/code.hpp>

#include <cstdint>
#include <functional>
#include <optional>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

[[noreturn]] void
throw_unsupported(char const *const message, char const *const function)
{
    MONAD_THROW(
        MonadException, message, "NullDb", function, __FILE__, __LINE__);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

bool NullDb::is_page_encoded() const
{
    return false;
}

std::optional<Account> NullDb::read_account(Address const &)
{
    return std::nullopt;
}

bytes32_t NullDb::read_storage(Address const &, Incarnation, bytes32_t const &)
{
    return {};
}

storage_page_t
NullDb::read_storage_page(Address const &, Incarnation, bytes32_t const &)
{
    return {};
}

vm::SharedIntercode NullDb::read_code(bytes32_t const &code_hash)
{
    // Only the empty code exists in an empty world; any other code hash must
    // have been introduced by a state override, which never reaches the db.
    if (code_hash != NULL_HASH) {
        throw_unsupported(
            "null database: code is unavailable", __PRETTY_FUNCTION__);
    }
    return vm::make_shared_intercode({});
}

BlockHeader NullDb::read_eth_header()
{
    throw_unsupported(
        "null database: block header is unavailable", __PRETTY_FUNCTION__);
}

bytes32_t NullDb::state_root()
{
    throw_unsupported(
        "null database: state root is unavailable", __PRETTY_FUNCTION__);
}

bytes32_t NullDb::receipts_root()
{
    throw_unsupported(
        "null database: receipts root is unavailable", __PRETTY_FUNCTION__);
}

bytes32_t NullDb::transactions_root()
{
    throw_unsupported(
        "null database: transactions root is unavailable", __PRETTY_FUNCTION__);
}

std::optional<bytes32_t> NullDb::withdrawals_root()
{
    throw_unsupported(
        "null database: withdrawals root is unavailable", __PRETTY_FUNCTION__);
}

void NullDb::set_block_and_prefix(
    uint64_t const block_number, bytes32_t const &)
{
    block_number_ = block_number;
}

void NullDb::finalize(uint64_t, bytes32_t const &)
{
    throw_unsupported(
        "null database: finalize is unsupported", __PRETTY_FUNCTION__);
}

void NullDb::update_verified_block(uint64_t)
{
    throw_unsupported(
        "null database: update_verified_block is unsupported",
        __PRETTY_FUNCTION__);
}

void NullDb::update_voted_metadata(uint64_t, bytes32_t const &)
{
    throw_unsupported(
        "null database: update_voted_metadata is unsupported",
        __PRETTY_FUNCTION__);
}

void NullDb::update_proposed_metadata(uint64_t, bytes32_t const &)
{
    throw_unsupported(
        "null database: update_proposed_metadata is unsupported",
        __PRETTY_FUNCTION__);
}

uint64_t NullDb::get_block_number() const
{
    return block_number_;
}

void NullDb::commit(
    bytes32_t const &, CommitBuilder &, BlockHeader const &,
    StateDeltas const &, std::function<void(BlockHeader &)>)
{
    throw_unsupported(
        "null database: commit is unsupported", __PRETTY_FUNCTION__);
}

MONAD_NAMESPACE_END
