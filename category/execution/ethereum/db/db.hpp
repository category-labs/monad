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
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/vm/code.hpp>

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

class CommitBuilder;

struct Db
{
    virtual bool is_page_encoded() const = 0;

    // True iff this db stores state in the EIP-8297 partitioned layout
    // (partitioned_layout.hpp).
    virtual bool is_partitioned() const
    {
        return false;
    }

    // Partitioned layout only: whether the account has a storage stem in the
    // state read by this db, i.e. a slot outside its header was ever written.
    virtual bool storage_bucket_exists(Address const &)
    {
        MONAD_ABORT("storage_bucket_exists requires a partitioned db");
    }

    virtual std::optional<Account> read_account(Address const &) = 0;

    // The account and, on a partitioned db, its header slots 0..63 which
    // share its leaf, so both come from one read. header_storage is nullopt
    // for an absent account and on every other layout.
    struct AccountRead
    {
        std::optional<Account> account;
        std::optional<storage_page_t> header_storage;
    };

    virtual AccountRead read_account_and_header(Address const &address)
    {
        return {.account = read_account(address), .header_storage = {}};
    }

    virtual bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) = 0;

    // Page-encoded db: the page at page_key. Partitioned db: page_key must
    // be partitioned::HEADER_PAGE_KEY and the result holds the account's
    // header slots 0..63 at offsets 0..63.
    virtual storage_page_t read_storage_page(
        Address const &, Incarnation, bytes32_t const &page_key) = 0;

    virtual vm::SharedIntercode read_code(bytes32_t const &) = 0;

    virtual BlockHeader read_eth_header() = 0;
    virtual bytes32_t state_root() = 0;
    virtual bytes32_t receipts_root() = 0;
    virtual bytes32_t transactions_root() = 0;
    virtual std::optional<bytes32_t> withdrawals_root() = 0;

    // empty block_id represents the finalized block
    virtual void set_block_and_prefix(
        uint64_t block_number, bytes32_t const &block_id = bytes32_t{}) = 0;
    virtual void finalize(uint64_t block_number, bytes32_t const &block_id) = 0;
    virtual void update_verified_block(uint64_t block_number) = 0;
    virtual void
    update_voted_metadata(uint64_t block_number, bytes32_t const &block_id) = 0;
    virtual void update_proposed_metadata(
        uint64_t block_number, bytes32_t const &block_id) = 0;

    virtual uint64_t get_block_number() const = 0;

    // two-stage commit
    virtual void commit(
        bytes32_t const &block_id, CommitBuilder &builder,
        BlockHeader const &header, StateDeltas const &state_deltas,
        std::function<void(BlockHeader &)> populate_header_fn) = 0;

    virtual std::string print_stats()
    {
        return {};
    }

protected:
    bytes32_t storage_lookup_key(bytes32_t const &key) const
    {
        return is_page_encoded() ? compute_page_key(key) : key;
    }
};

MONAD_NAMESPACE_END
