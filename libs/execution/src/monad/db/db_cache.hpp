#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_hash_compare.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/lru/lru_cache.hpp>
#include <monad/state2/state_deltas.hpp>

#include <evmc/evmc.hpp>

#include <thread-safe-lru/lru-cache.h>

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
    using CodeCache =
        tstarling::ThreadSafeLRUCache<bytes32_t, std::shared_ptr<CodeAnalysis>>;

    AccountsCache accounts_{10'000'000};
    StorageCache storage_{10'000'000};
    CodeCache code_{40000};

public:
    DbCache(Db &db)
        : db_{db}
    {
    }

    virtual std::optional<Account> read_account(Address const &address) override
    {
        {
            AccountsCache::ConstAccessor acc{};
            if (accounts_.find(acc, address)) {
                return acc->second.value_;
            }
        }
        auto const result = db_.read_account(address);
        accounts_.insert(address, result);
        return result;
    }

    virtual bytes32_t read_storage(
        Address const &address, Incarnation incarnation,
        bytes32_t const &key) override
    {
        StorageKey const skey{address, incarnation, key};
        {
            StorageCache::ConstAccessor acc{};
            if (storage_.find(acc, skey)) {
                return acc->second.value_;
            }
        }
        auto const result = db_.read_storage(address, incarnation, key);
        storage_.insert(skey, result);
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

    virtual void set_block_and_round(uint64_t, uint64_t) override
    {
        MONAD_ABORT("TODO: DbCache does not support proposal execution");
    }

    virtual void finalize(uint64_t, uint64_t) override
    {
        MONAD_ABORT("TODO: DbCache does not support proposal execution");
    }

    virtual void update_verified_block(uint64_t) override
    {
        MONAD_ABORT("TODO: DbCache does not support proposal execution");
    }

    virtual void commit(
        StateDeltas const &state_deltas, Code const &code,
        BlockHeader const &header, std::vector<Receipt> const &receipts,
        std::vector<std::vector<CallFrame>> const &call_frames,
        std::vector<Transaction> const &transactions,
        std::vector<BlockHeader> const &ommers,
        std::optional<std::vector<Withdrawal>> const &withdrawals,
        std::optional<uint64_t> const round_number) override
    {
        db_.commit(
            state_deltas,
            code,
            header,
            receipts,
            call_frames,
            transactions,
            ommers,
            withdrawals);

        for (auto it = state_deltas.cbegin(); it != state_deltas.cend(); ++it) {
            auto const &address = it->first;
            auto const &account_delta = it->second.account;
            if (account_delta.second != account_delta.first) {
                accounts_.insert(address, account_delta.second);
            }
            auto const &storage = it->second.storage;
            auto const &account = account_delta.second;
            for (auto it2 = storage.cbegin(); it2 != storage.cend(); ++it2) {
                auto const &key = it2->first;
                auto const &storage_delta = it2->second;
                if (storage_delta.second != storage_delta.first) {
                    if (account.has_value()) {
                        auto const incarnation = account->incarnation;
                        storage_.insert(
                            StorageKey(address, incarnation, key),
                            storage_delta.second);
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
        return db_.print_stats() + " | " + accounts_.print_stats() + " | " +
               storage_.print_stats();
    }
};

MONAD_NAMESPACE_END
