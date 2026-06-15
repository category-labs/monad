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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/vm/vm.hpp>

#include <category/core/hex.hpp>

#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

// Read-only Db over an mpt::RODb. Storage reads are encoding-aware: the
// encoding is taken from the bound timeline's persisted state_machine_kind
// (monad == page-encoded), mirroring TrieDb.
class TrieRODb final : public ::monad::Db
{
    ::monad::mpt::RODb &db_;
    uint64_t block_number_;
    ::monad::mpt::NodeCursor prefix_cursor_;
    bool page_encoded_;

public:
    explicit TrieRODb(mpt::RODb &db)
        : db_(db)
        , block_number_(mpt::INVALID_BLOCK_NUM)
        , prefix_cursor_()
        , page_encoded_(
              db.state_machine_type() == mpt::state_machine_kind::monad)
    {
    }

    ~TrieRODb() = default;

    virtual bool is_page_encoded() const override
    {
        return page_encoded_;
    }

    virtual void set_block_and_prefix(
        uint64_t const block_number,
        bytes32_t const &block_id = bytes32_t{}) override
    {
        auto const prefix = block_id == bytes32_t{} ? finalized_nibbles
                                                    : proposal_prefix(block_id);
        auto res = db_.find(prefix, block_number);
        if (res.has_error()) {
            MONAD_ASSERT_PRINTF(
                res.assume_error() ==
                    ::monad::mpt::DbError::version_no_longer_exist,
                "Cannot find block_id %s prefix at block %lu where block is "
                "still valid in db",
                to_hex(to_byte_string_view(block_id.bytes)).c_str(),
                block_number);
            MONAD_ASSERT_THROW(
                res.has_value(),
                "Block was invalidated in db while execution was in progress");
        }
        prefix_cursor_ = res.value();
        block_number_ = block_number;
    }

    virtual std::optional<Account> read_account(Address const &addr) override
    {
        auto acc_leaf_res = db_.find(
            prefix_cursor_,
            mpt::concat(
                STATE_NIBBLE,
                mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
            block_number_);
        if (!acc_leaf_res.has_value()) {
            MONAD_ASSERT_THROW(
                acc_leaf_res.assume_error() !=
                    ::monad::mpt::DbError::version_no_longer_exist,
                "Block was invalidated in db while execution was in progress");
            return std::nullopt;
        }
        auto encoded_account = acc_leaf_res.value().node->value();
        auto const acct = decode_account_db_ignore_address(encoded_account);
        return acct.value();
    }

    virtual bytes32_t read_storage(
        Address const &addr, Incarnation, bytes32_t const &key) override
    {
        // Page-encoded storage is keyed by keccak(page_key) and the value is
        // an encoded page; slot-encoded storage is keyed by keccak(slot). Look
        // up the right node and decode it accordingly (mirrors TrieDb).
        bytes32_t const lookup_key =
            page_encoded_ ? compute_page_key(key) : key;
        auto storage_leaf_res = db_.find(
            prefix_cursor_,
            mpt::concat(
                STATE_NIBBLE,
                mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
                mpt::NibblesView{
                    keccak256({lookup_key.bytes, sizeof(lookup_key.bytes)})}),
            block_number_);
        if (!storage_leaf_res.has_value()) {
            MONAD_ASSERT_THROW(
                storage_leaf_res.assume_error() !=
                    ::monad::mpt::DbError::version_no_longer_exist,
                "Block was invalidated in db while execution was in progress");
            return {};
        }
        auto encoded_storage = storage_leaf_res.value().node->value();
        if (page_encoded_) {
            auto const page = decode_storage_page_leaf(encoded_storage);
            MONAD_ASSERT(!page.has_error());
            return page.value()[compute_slot_offset(key)];
        }
        auto const storage = decode_storage_db_ignore_key(encoded_storage);
        MONAD_ASSERT(!storage.has_error());
        return to_bytes(storage.value());
    }

    virtual storage_page_t read_storage_page(
        Address const &addr, Incarnation, bytes32_t const &page_key) override
    {
        MONAD_ASSERT(
            page_encoded_,
            "read_storage_page is only valid on a page-encoded TrieRODb");
        auto storage_leaf_res = db_.find(
            prefix_cursor_,
            mpt::concat(
                STATE_NIBBLE,
                mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
                mpt::NibblesView{
                    keccak256({page_key.bytes, sizeof(page_key.bytes)})}),
            block_number_);
        if (!storage_leaf_res.has_value()) {
            MONAD_ASSERT_THROW(
                storage_leaf_res.assume_error() !=
                    ::monad::mpt::DbError::version_no_longer_exist,
                "Block was invalidated in db while execution was in progress");
            return {};
        }
        auto const encoded_storage = storage_leaf_res.value().node->value();
        auto const page = decode_storage_page_leaf(encoded_storage);
        MONAD_ASSERT(!page.has_error());
        return page.value();
    }

    virtual vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        // TODO read intercode object
        auto code_leaf_res = db_.find(
            prefix_cursor_,
            mpt::concat(
                CODE_NIBBLE,
                mpt::NibblesView{to_byte_string_view(code_hash.bytes)}),
            block_number_);
        if (!code_leaf_res.has_value()) {
            MONAD_ASSERT_THROW(
                code_leaf_res.assume_error() !=
                    ::monad::mpt::DbError::version_no_longer_exist,
                "Block was invalidated in db while execution was in progress");
            return vm::make_shared_intercode({});
        }
        return vm::make_shared_intercode(code_leaf_res.value().node->value());
    }

    virtual void commit(
        bytes32_t const &, CommitBuilder &, BlockHeader const &,
        StateDeltas const &, std::function<void(BlockHeader &)>) override
    {
        MONAD_ABORT();
    }

    virtual void finalize(uint64_t, bytes32_t const &) override
    {
        MONAD_ABORT();
    }

    virtual void update_verified_block(uint64_t) override
    {
        MONAD_ABORT();
    }

    virtual void update_voted_metadata(uint64_t, bytes32_t const &) override
    {
        MONAD_ABORT();
    }

    virtual void update_proposed_metadata(uint64_t, bytes32_t const &) override
    {
        MONAD_ABORT();
    }

    virtual BlockHeader read_eth_header() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t state_root() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t receipts_root() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t transactions_root() override
    {
        MONAD_ABORT();
    }

    virtual std::optional<bytes32_t> withdrawals_root() override
    {
        MONAD_ABORT();
    }

    virtual uint64_t get_block_number() const override
    {
        return block_number_;
    }
};

MONAD_NAMESPACE_END
