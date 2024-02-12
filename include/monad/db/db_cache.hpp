#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/state_deltas.hpp>

#include <evmc/evmc.hpp>

#include <thread-safe-lru/lru-cache.h>

#include <boost/container_hash/hash.hpp>

#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

class DbCache final : public Db
{
    Db &db_;

    struct HashCompare
    {
        size_t hash(std::pair<Address, bytes32_t> const &p) const
        {
            return boost::hash_value(p);
        }

        bool equal(auto const &p1, auto const &p2) const
        {
            return p1 == p2;
        }
    };

    using AccountCache =
        tstarling::ThreadSafeLRUCache<Address, std::optional<Account>>;
    using StorageCache = tstarling::ThreadSafeLRUCache<
        std::pair<Address, bytes32_t>, bytes32_t, HashCompare>;

    AccountCache accounts_{10000000};
    StorageCache storage_{10000000};

public:
    DbCache(Db &db)
        : db_{db}
    {
    }

    virtual std::optional<Account> read_account(Address const &address) override
    {
        AccountCache::ConstAccessor it{};
        if (accounts_.find(it, address)) {
            auto result = *it;
            if (result.has_value()) {
                result->incarnation = 0;
            }
            return result;
        }
        {
            auto const result = db_.read_account(address);
            accounts_.insert(address, result);
            return result;
        }
    }

    virtual bytes32_t
    read_storage(Address const &address, bytes32_t const &key) override
    {
        StorageCache::ConstAccessor it{};
        if (storage_.find(it, {address, key})) {
            return *it;
        }
        {
            bytes32_t const result = db_.read_storage(address, key);
            storage_.insert({address, key}, result);
            return result;
        }
    }

    virtual byte_string read_code(bytes32_t const &code_hash) override
    {
        return db_.read_code(code_hash);
    }

    virtual void
    commit(StateDeltas const &state_deltas, Code const &code) override
    {
        db_.commit(state_deltas, code);
        for (auto it = state_deltas.cbegin(); it != state_deltas.cend(); ++it) {
            auto const &address = it->first;
            auto const &account_delta = it->second.account;
            if (account_delta.second != account_delta.first) {
                accounts_.insert(address, account_delta.second);
            }
            auto const &storage = it->second.storage;
            for (auto it2 = storage.cbegin(); it2 != storage.cend(); ++it2) {
                auto const &key = it2->first;
                auto const &storage_delta = it2->second;
                if (storage_delta.second != storage_delta.first) {
                    storage_.insert({address, key}, storage_delta.second);
                }
            }
        }
    }

    virtual bytes32_t state_root() override
    {
        return db_.state_root();
    }

    virtual void
    create_and_prune_block_history(uint64_t const block_number) const override
    {
        return db_.create_and_prune_block_history(block_number);
    }
};

MONAD_NAMESPACE_END
