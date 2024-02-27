#pragma once

#include <monad/cache/account_storage_cache.hpp>
#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/state2/state_deltas.hpp>

#include <evmc/evmc.hpp>

#include <thread-safe-lru/lru-cache.h>

#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

class DbCache final : public DbRW
{
    DbRW &db_;

    using Combined = AccountStorageCache;

    Combined cache_{10'000'000, 10'000'000};

    using CodeCache =
        tstarling::ThreadSafeLRUCache<bytes32_t, std::shared_ptr<CodeAnalysis>>;

    CodeCache code_{40000};

public:
    DbCache(DbRW &db)
        : db_{db}
    {
    }

    virtual std::optional<Account> read_account(Address const &address) override
    {
        {
            Combined::AccountConstAccessor acc{};
            if (cache_.find_account(acc, address)) {
                auto result = acc->second.value_;
                if (result.has_value()) {
                    result->incarnation = 0;
                }
                return result;
            }
        }
        auto const result = db_.read_account(address);
        {
            Combined::AccountAccessor acc{};
            cache_.insert_account(acc, address, result);
        }
        return result;
    }

    virtual bytes32_t
    read_storage(Address const &address, bytes32_t const &key) override
    {
        {
            Combined::StorageConstAccessor acc{};
            if (cache_.find_storage(acc, address, key)) {
                return acc->second.value_;
            }
        }
        auto const result = db_.read_storage(address, key);
        {
            Combined::AccountAccessor acc{};
            if (!cache_.find_account(acc, address)) {
                auto const account = db_.read_account(address);
                MONAD_ASSERT(account);
                cache_.insert_account(acc, address, account);
            }
            cache_.insert_storage(acc, key, result);
        }
        return result;
    }

    virtual std::shared_ptr<CodeAnalysis>
    read_code(bytes32_t const &code_hash) override
    {
        {
            CodeCache::ConstAccessor it{};
            if (code_.find(it, code_hash)) {
                return *it;
            }
        }
        {
            auto const code_analysis = db_.read_code(code_hash);
            code_.insert(code_hash, code_analysis);
            return code_analysis;
        }
    }

    virtual void increment_block_number() override
    {
        db_.increment_block_number();
    }

    virtual void commit(
        StateDeltas const &state_deltas, Code const &code,
        std::vector<Receipt> const &receipts) override
    {
        db_.commit(state_deltas, code, receipts);

        for (auto it = state_deltas.cbegin(); it != state_deltas.cend(); ++it) {
            auto const &address = it->first;
            auto const &account_delta = it->second.account;
            if (account_delta.second != account_delta.first) {
                Combined::AccountAccessor acc{};
                cache_.insert_account(acc, address, account_delta.second);
            }
            auto const &storage = it->second.storage;
            for (auto it2 = storage.cbegin(); it2 != storage.cend(); ++it2) {
                auto const &key = it2->first;
                auto const &storage_delta = it2->second;
                if (storage_delta.second != storage_delta.first) {
                    Combined::AccountAccessor acc{};
                    bool const found = cache_.find_account(acc, address);
                    if (found) {
                        cache_.insert_storage(acc, key, storage_delta.second);
                    }
                }
            }
        }

        for (auto const &[code_hash, code_analysis] : code) {
            CodeCache::ConstAccessor it{};
            if (!code_.find(it, code_hash)) {
                code_.insert(code_hash, code_analysis);
            }
        }
    }

    virtual bytes32_t state_root() override
    {
        return db_.state_root();
    }

    virtual bytes32_t receipts_root() override
    {
        return db_.receipts_root();
    }

    virtual void
    create_and_prune_block_history(uint64_t const block_number) const override
    {
        return db_.create_and_prune_block_history(block_number);
    }
};

MONAD_NAMESPACE_END
