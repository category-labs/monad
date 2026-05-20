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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/bytes_hash_compare.hpp>
#include <category/core/config.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/state2/proposal_state.hpp>
#include <category/vm/utils/lru_weight_cache.hpp>

#include <cstdint>
#include <cstring>
#include <format>
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
    using StorageCache = vm::utils::LruWeightCache<
        StorageKey, byte_string, StorageKeyHashCompare>;

    static constexpr uint32_t STORAGE_CACHE_MAX_BYTES = 256u * 1024 * 1024;

    AccountsCache accounts_{10'000'000};
    StorageCache storage_{STORAGE_CACHE_MAX_BYTES};
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

    // TODO: switch to a templated `F&& on_found` callback that takes a
    // byte_string_view (pinned into the cache / proposal state) once
    // ProposalPostState holds encoded pages — both sources will then expose
    // pinned byte_strings and the extra copy here becomes unnecessary.
    bool try_read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key, byte_string &result)
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
            // Finalizing a truncated proposal. Clear LRU caches.  This is an
            // expensive operation. However, with 100 unfinalized propoals,
            // cache speed is the least of our problems.
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
        return std::format(
            "{:8} / {:10}", storage_.size(), storage_.approx_weight());
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
                    byte_string const v{
                        compact_storage_view(storage_delta.second)};
                    storage_.insert(
                        StorageKey(address, incarnation, key),
                        v,
                        static_cast<uint32_t>(v.size()));
                }
            }
        }
    }
};

MONAD_NAMESPACE_END
