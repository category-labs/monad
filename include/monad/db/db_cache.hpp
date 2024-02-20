#pragma once

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

class DbCache final : public Db
{
    Db &db_;

    using AccountCache =
        tstarling::ThreadSafeLRUCache<Address, std::optional<Account>>;

    AccountCache accounts_{10000000};

    using CodeCache =
        tstarling::ThreadSafeLRUCache<bytes32_t, std::shared_ptr<CodeAnalysis>>;

    CodeCache code_{40000};

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
        return db_.read_storage(address, key);
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

    virtual void
    create_and_prune_block_history(uint64_t const block_number) const override
    {
        return db_.create_and_prune_block_history(block_number);
    }
};

MONAD_NAMESPACE_END
