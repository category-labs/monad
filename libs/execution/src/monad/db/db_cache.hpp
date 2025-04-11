#pragma once

#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_hash_compare.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/lru/lru_cache.hpp>
#include <monad/state2/proposal_state.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/vm/evmone/code_analysis.hpp>

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
    using CodeCache = LruCache<bytes32_t, std::shared_ptr<CodeAnalysis>>;

    AccountsCache accounts_{10'000'000};
    StorageCache storage_{10'000'000};
    CodeCache code_{40000};
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

    virtual std::shared_ptr<CodeAnalysis>
    read_code(bytes32_t const &code_hash) override
    {
        bool truncated = false;
        std::shared_ptr<CodeAnalysis> result;
        if (proposals_.try_read_code(code_hash, result, truncated)) {
            return result;
        }
        if (!truncated) {
            CodeCache::ConstAccessor it{};
            if (code_.find(it, code_hash)) {
                return it->second.value_;
            }
        }
        return db_.read_code(code_hash);
    }

    virtual void set_block_and_round(
        uint64_t const block_number,
        std::optional<uint64_t> const round_number = {}) override
    {
        proposals_.set_block_and_round(block_number, round_number);
        db_.set_block_and_round(block_number, round_number);
    }

    virtual void
    finalize(uint64_t const block_number, uint64_t const round_number) override
    {
        std::unique_ptr<ProposalState> const ps =
            proposals_.finalize(block_number, round_number);
        if (ps) {
            insert_in_lru_caches(ps->state(), ps->code());
        }
        else {
            // Finalizing a truncated proposal. Clear LRU caches.
            accounts_.clear();
            storage_.clear();
            code_.clear();
        }
        db_.finalize(block_number, round_number);
    }

    virtual void update_verified_block(uint64_t const block_number) override
    {
        db_.update_verified_block(block_number);
    }

    virtual void update_voted_metadata(
        uint64_t const block_number, uint64_t const round) override
    {
        db_.update_voted_metadata(block_number, round);
    }

    virtual void commit(
        StateDeltas const &, Code const &, MonadConsensusBlockHeader const &,
        std::vector<Receipt> const &,
        std::vector<std::vector<CallFrame>> const &,
        std::vector<Address> const &, std::vector<Transaction> const &,
        std::vector<BlockHeader> const &,
        std::optional<std::vector<Withdrawal>> const &) override
    {
        MONAD_ABORT("Use DbCache commit with unique_ptr args.");
    }

    virtual void commit(
        std::unique_ptr<StateDeltas> state_deltas, std::unique_ptr<Code> code,
        MonadConsensusBlockHeader const &consensus_header,
        std::vector<Receipt> const &receipts = {},
        std::vector<std::vector<CallFrame>> const &call_frames = {},
        std::vector<Address> const &senders = {},
        std::vector<Transaction> const &transactions = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const &withdrawals = {}) override
    {
        db_.commit(
            *state_deltas,
            *code,
            consensus_header,
            receipts,
            call_frames,
            senders,
            transactions,
            ommers,
            withdrawals);
        proposals_.commit(
            std::move(state_deltas), std::move(code), consensus_header.round);
        MONAD_ASSERT(!state_deltas);
        MONAD_ASSERT(!code);
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
        return db_.print_stats() + " | " + accounts_.print_stats() + " | " +
               storage_.print_stats();
    }

private:
    void insert_in_lru_caches(StateDeltas const &state_deltas, Code const &code)
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
        for (auto const &[code_hash, code_analysis] : code) {
            CodeCache::ConstAccessor it{};
            if (!code_.find(it, code_hash)) {
                code_.insert(code_hash, code_analysis);
            }
        }
    }
};

MONAD_NAMESPACE_END
