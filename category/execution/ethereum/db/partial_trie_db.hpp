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

// Db backed by a witness-derived partial trie (see offset_trie.hpp).

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <functional>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

using CodeIndex = ankerl::unordered_dense::map<bytes32_t, vm::SharedIntercode>;

class PartialTrieDb final : public Db
{
    mpt::OffsetTrie trie_;
    // The EVM reads an account's slots in bursts, and read_storage keccaks the
    // address and re-descends the account trie for every one. Both reads are of
    // the pre-state trie, which is immutable for the whole block, so one entry
    // is sound and never needs invalidating.
    mutable Address sroot_addr_{};
    mutable mpt::NodeId sroot_id_{mpt::NULL_ID};
    mutable bool sroot_valid_{false};
    CodeIndex codes_;
    uint64_t block_number_{0};
    BlockHeader last_committed_header_{};

public:
    PartialTrieDb(mpt::OffsetTrie trie, CodeIndex codes)
        : trie_(std::move(trie))
        , codes_(std::move(codes))
    {
    }

public:
    PartialTrieDb() = delete;

    // TODO: update impl to make it work with page-encoded storage
    bool is_page_encoded() const override
    {
        return false;
    }

    std::optional<Account> read_account(Address const &) override;

    bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &) override;

    storage_page_t
    read_storage_page(Address const &, Incarnation, bytes32_t const &) override
    {
        MONAD_ABORT("PartialTrieDb: read_storage_page unsupported");
    }

    vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        auto const it = codes_.find(code_hash);
        return it == codes_.end() ? vm::make_shared_intercode({}) : it->second;
    }

    BlockHeader read_eth_header() override
    {
        return last_committed_header_;
    }

    bytes32_t state_root() override
    {
        return trie_.state_root();
    }

    bytes32_t receipts_root() override
    {
        return last_committed_header_.receipts_root;
    }

    bytes32_t transactions_root() override
    {
        return last_committed_header_.transactions_root;
    }

    std::optional<bytes32_t> withdrawals_root() override
    {
        return last_committed_header_.withdrawals_root;
    }

    uint64_t get_block_number() const override
    {
        return block_number_;
    }

    void set_block_and_prefix(
        uint64_t const block_number, bytes32_t const &) override
    {
        block_number_ = block_number;
    }

    void commit(
        bytes32_t const &block_id, CommitBuilder &, BlockHeader const &,
        StateDeltas const &, std::function<void(BlockHeader &)>) override;

    // No-op overrides for operations that are irrelevant in the witness
    // context.
    void finalize(uint64_t, bytes32_t const &) override {}

    void update_verified_block(uint64_t) override {}

    void update_voted_metadata(uint64_t, bytes32_t const &) override {}

    void update_proposed_metadata(uint64_t, bytes32_t const &) override {}
};

MONAD_NAMESPACE_END
