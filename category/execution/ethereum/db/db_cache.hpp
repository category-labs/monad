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
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/state2/proposal_state.hpp>

#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <string>

MONAD_NAMESPACE_BEGIN

class DbCache final
{
    struct StorageKey
    {
        static constexpr size_t k_bytes =
            sizeof(Address) + sizeof(Incarnation) + sizeof(bytes32_t);

        uint8_t bytes[k_bytes];

        StorageKey() = default;

        StorageKey(
            Address const &addr, Incarnation const incarnation,
            bytes32_t const &key)
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
    DbCache() = default;

    bool
    try_read_account(Address const &address, std::optional<Account> &result)
    {
        auto const res = proposals_.try_read_account(address, result);
        if (res.found) {
            return true;
        }
        if (!res.truncated) {
            AccountsCache::ConstAccessor acc{};
            if (accounts_.find(acc, address)) {
                result = acc->second.value_;
                return true;
            }
        }
        return false;
    }

    bool try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, bytes32_t &result)
    {
        auto const res =
            proposals_.try_read_storage(address, incarnation, key, result);
        if (res.found) {
            return true;
        }
        if (!res.truncated) {
            StorageKey const skey{address, incarnation, key};
            StorageCache::ConstAccessor acc{};
            if (storage_.find(acc, skey)) {
                result = acc->second.value_;
                return true;
            }
        }
        return false;
    }

    void
    set_block_and_prefix(uint64_t const block_number, bytes32_t const &block_id)
    {
        proposals_.set_block_and_prefix(block_number, block_id);
    }

    void update_proposal_state(
        std::unique_ptr<StateDeltas> state_deltas, uint64_t const block_number,
        bytes32_t const &block_id)
    {
        MONAD_ASSERT(state_deltas);
        proposals_.commit(std::move(state_deltas), block_number, block_id);
    }

    void on_finalize(uint64_t const block_number, bytes32_t const &block_id)
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
    }

    std::string accounts_stats()
    {
        return accounts_.print_stats();
    }

    std::string storage_stats()
    {
        return storage_.print_stats();
    }

private:
    void insert_in_lru_caches(StateDeltas const &state_deltas)
    {
        for (auto const &[address, delta] : state_deltas) {
            auto const &account_delta = delta.account;
            accounts_.insert(address, account_delta.second);
            auto const &storage = delta.storage;
            auto const &account = account_delta.second;
            if (account.has_value()) {
                for (auto const &[key, storage_delta] : storage) {
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
