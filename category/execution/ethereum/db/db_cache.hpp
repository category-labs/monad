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

#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/monad/state2/proposal_state.hpp>
#include <category/vm/vm.hpp>

#include <evmc/evmc.hpp>

#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

class DbCache final : public Db
{
    Db &db_;

    struct StorageKey
    {
        static constexpr size_t k_bytes =
            sizeof(Address) + sizeof(Incarnation) + sizeof(bytes32_t);

        uint8_t bytes[k_bytes];

        StorageKey() = default;

        StorageKey(
            Address const &addr, Incarnation incarnation, bytes32_t const &key)
        {
            memcpy(bytes, addr.bytes, sizeof(Address));
            memcpy(&bytes[sizeof(Address)], &incarnation, sizeof(Incarnation));
            memcpy(
                &bytes[sizeof(Address) + sizeof(Incarnation)],
                key.bytes,
                sizeof(bytes32_t));
        }
    };

    using AddressHashCompare = BytesHashCompare<Address>;
    using StorageKeyHashCompare = BytesHashCompare<StorageKey>;
    using AccountsCache =
        LruCache<Address, std::optional<Account>, AddressHashCompare>;
    using StorageCache = LruCache<StorageKey, bytes32_t, StorageKeyHashCompare>;

    AccountsCache accounts_{10'000'000};
    StorageCache storage_{10'000'000};
    Proposals proposals_;

public:
    DbCache(Db &db)
        : db_{db}
    {
    }

    virtual std::optional<Account> read_account(Address const &address) override
    {
        bool truncated = false; // ancestors truncated
        std::optional<Account> result;
        if (proposals_.try_read_account(address, result, truncated)) {
            return result;
        }
        if (!truncated) {
            AccountsCache::ConstAccessor acc{};
            if (accounts_.find(acc, address)) {
                return acc->second.value_;
            }
        }
        return db_.read_account(address);
    }

    virtual bytes32_t read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key) override
    {
        bool truncated = false;
        bytes32_t result;
        if (proposals_.try_read_storage(
                address, incarnation, key, result, truncated)) {
            return result;
        }
        if (!truncated) {
            StorageKey const skey{address, incarnation, key};
            StorageCache::ConstAccessor acc{};
            if (storage_.find(acc, skey)) {
                return acc->second.value_;
            }
        }
        return db_.read_storage(address, incarnation, key);
    }

    virtual vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        return db_.read_code(code_hash);
    }

    virtual void set_block_and_prefix(
        uint64_t const block_number,
        bytes32_t const &block_id = bytes32_t{}) override
    {
        proposals_.set_block_and_prefix(block_number, block_id);
        db_.set_block_and_prefix(block_number, block_id);
    }

    virtual void
    finalize(uint64_t const block_number, bytes32_t const &block_id) override
    {
        std::unique_ptr<ProposalState> const ps =
            proposals_.finalize(block_number, block_id);
        if (ps) {
            insert_in_lru_caches(ps->state());
        }
        else {
            // Finalizing a truncated proposal. Clear LRU caches.
            accounts_.clear();
            storage_.clear();
        }
        db_.finalize(block_number, block_id);
    }

    virtual void update_verified_block(uint64_t const block_number) override
    {
        db_.update_verified_block(block_number);
    }

    virtual void update_voted_metadata(
        uint64_t const block_number, bytes32_t const &block_id) override
    {
        db_.update_voted_metadata(block_number, block_id);
    }

    virtual void commit(
        StateDeltas const &, Code const &, bytes32_t const &,
        BlockHeader const &, std::vector<Receipt> const &,
        std::vector<std::vector<CallFrame>> const &,
        std::vector<Address> const &, std::vector<Transaction> const &,
        std::vector<BlockHeader> const &,
        std::optional<std::vector<Withdrawal>> const &) override
    {
        MONAD_ABORT("Use DbCache commit with unique_ptr arg.");
    }

    virtual void commit(
        std::unique_ptr<StateDeltas> state_deltas, Code const &code,
        bytes32_t const &block_id, BlockHeader const &header,
        std::vector<Receipt> const &receipts = {},
        std::vector<std::vector<CallFrame>> const &call_frames = {},
        std::vector<Address> const &senders = {},
        std::vector<Transaction> const &transactions = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const &withdrawals = {}) override
    {
        db_.commit(
            *state_deltas,
            code,
            block_id,
            header,
            receipts,
            call_frames,
            senders,
            transactions,
            ommers,
            withdrawals);

        proposals_.commit(std::move(state_deltas), header.number, block_id);
    }

    virtual BlockHeader read_eth_header() override
    {
        return db_.read_eth_header();
    }

    virtual bytes32_t state_root() override
    {
        return db_.state_root();
    }

    virtual bytes32_t receipts_root() override
    {
        return db_.receipts_root();
    }

    virtual bytes32_t transactions_root() override
    {
        return db_.transactions_root();
    }

    virtual std::optional<bytes32_t> withdrawals_root() override
    {
        return db_.withdrawals_root();
    }

    virtual std::string print_stats() override
    {
        return db_.print_stats() + ",ac=" + accounts_.print_stats() +
               ",sc=" + storage_.print_stats();
    }

    virtual uint64_t get_block_number() const override
    {
        return db_.get_block_number();
    }

private:
    void insert_in_lru_caches(StateDeltas const &state_deltas)
    {
        for (auto it = state_deltas.cbegin(); it != state_deltas.cend(); ++it) {
            auto const &address = it->first;
            auto const &account_delta = it->second.account;
            accounts_.insert(address, account_delta.second);
            auto const &storage = it->second.storage;
            auto const &account = account_delta.second;
            if (account.has_value()) {
                for (auto it2 = storage.cbegin(); it2 != storage.cend();
                     ++it2) {
                    auto const &key = it2->first;
                    auto const &storage_delta = it2->second;
                    auto const incarnation = account->incarnation;
                    storage_.insert(
                        StorageKey(address, incarnation, key),
                        storage_delta.second);
                }
            }
        }
    }
};

MONAD_NAMESPACE_END
