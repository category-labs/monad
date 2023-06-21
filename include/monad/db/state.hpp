#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/db/config.hpp>

#include <vector>

MONAD_DB_NAMESPACE_BEGIN

template <class TAccountStore, class TValueStore, class TCodeStore, class TBlockCache>
struct State
{
    struct WorkingCopy
    {
        typename TAccountStore::WorkingCopy accounts_;
        typename TValueStore::WorkingCopy storage_;
        typename TCodeStore::WorkingCopy code_;
        std::vector<Receipt::Log> logs_{};
        TBlockCache &block_cache_{};
        unsigned int txn_id_{};

        WorkingCopy(
            unsigned int i, typename TAccountStore::WorkingCopy &&a,
            typename TValueStore::WorkingCopy &&s,
            typename TCodeStore::WorkingCopy &&c,
            TBlockCache &b)
            : accounts_{std::move(a)}
            , storage_{std::move(s)}
            , code_{std::move(c)}
            , block_cache_{b}
            , txn_id_{i}
        {
        }

        unsigned int txn_id() const noexcept { return txn_id_; }
        void create_contract(address_t const &a) noexcept
        {
            accounts_.create_contract(a);
        }

        // EVMC Host Interface
        [[nodiscard]] bool account_exists(address_t const &a) const
        {
            return accounts_.account_exists(a);
        }

        // EVMC Host Interface
        evmc_access_status access_account(address_t const &a) noexcept
        {
            return accounts_.access_account(a);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t get_balance(address_t const &a) const noexcept
        {
            return accounts_.get_balance(a);
        }

        void set_balance(address_t const &a, uint256_t const &b)
        {
            accounts_.set_balance(a, b);
        }

        [[nodiscard]] auto get_nonce(address_t const &a) const noexcept
        {
            return accounts_.get_nonce(a);
        }

        void set_nonce(address_t const &a, uint64_t nonce) noexcept
        {
            accounts_.set_nonce(a, nonce);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t get_code_hash(address_t const &a) const noexcept
        {
            return accounts_.get_code_hash(a);
        }

        [[nodiscard]] bool selfdestruct(address_t const &a, address_t const &b)
        {
            return accounts_.selfdestruct(a, b);
        }

        void destruct_suicides() { accounts_.destruct_suicides(); }

        void destruct_touched_dead() { accounts_.destruct_touched_dead(); }

        uint64_t total_selfdestructs() const noexcept
        {
            return accounts_.total_selfdestructs();
        }

        // EVMC Host Interface
        evmc_access_status
        access_storage(address_t const &a, bytes32_t const &key)
        {
            return storage_.access_storage(a, key);
        }

        // EVMC Host Interface
        [[nodiscard]] bytes32_t
        get_storage(address_t const &a, bytes32_t const &key) const noexcept
        {
            return storage_.get_storage(a, key);
        }

        // EVMC Host Interface
        [[nodiscard]] evmc_storage_status set_storage(
            address_t const &a, bytes32_t const &key, bytes32_t const &value)
        {
            return storage_.set_storage(a, key, value);
        }

        // Account contract accesses
        void set_code(address_t const &a, byte_string const &c)
        {
            code_.set_code(a, c);
        }

        // EVMC Host Interface
        [[nodiscard]] size_t get_code_size(address_t const &a) const noexcept
        {
            return code_.get_code_size(a);
        }

        // EVMC Host Interface
        [[nodiscard]] size_t copy_code(
            address_t const &a, size_t offset, uint8_t *buffer,
            size_t size) const noexcept
        {
            return code_.copy_code(a, offset, buffer, size);
        }

        [[nodiscard]] byte_string_view
        get_code(address_t const &a) const noexcept
        {
            return code_.code_at(a);
        }

        void revert() noexcept
        {
            accounts_.revert();
            storage_.revert();
            code_.revert();
        }

        // Logs
        void store_log(Receipt::Log &&l) { logs_.emplace_back(l); }

        std::vector<Receipt::Log> &logs() { return logs_; }
    };

    enum class MergeStatus
    {
        WILL_SUCCEED,
        TRY_LATER,
        COLLISION_DETECTED,
    };

    TAccountStore &accounts_;
    TValueStore &storage_;
    TCodeStore &code_;
    TBlockCache &block_cache_{};
    unsigned int current_txn_{};

    State(TAccountStore &a, TValueStore &s, TCodeStore &c, TBlockCache &bc)
        : accounts_{a}
        , storage_{s}
        , code_{c}
        , block_cache_{bc}
    {
    }

    [[nodiscard]] bytes32_t get_block_hash(int64_t number) const noexcept
    {
        return block_cache_.get_block_hash(number);
    }

    unsigned int current_txn() const { return current_txn_; }

    WorkingCopy get_working_copy(unsigned int id) const
    {
        return WorkingCopy(
            id,
            typename TAccountStore::WorkingCopy{accounts_},
            typename TValueStore::WorkingCopy{storage_},
            typename TCodeStore::WorkingCopy{code_},
            block_cache_);
    }

    MergeStatus can_merge_changes(WorkingCopy const &c) const
    {
        if (current_txn() != c.txn_id()) {
            return MergeStatus::TRY_LATER;
        }

        if (accounts_.can_merge(c.accounts_) &&
            storage_.can_merge(c.storage_) && code_.can_merge(c.code_)) {
            return MergeStatus::WILL_SUCCEED;
        }
        return MergeStatus::COLLISION_DETECTED;
    }

    void merge_changes(WorkingCopy &c)
    {
        accounts_.merge_changes(c.accounts_);
        storage_.merge_touched(c.storage_);
        code_.merge_changes(c.code_);
        ++current_txn_;
    }

    bool can_commit() const
    {
        return accounts_.can_commit() && storage_.can_commit() &&
               code_.can_commit();
    }

    void commit()
    {
        // Note: storage updates must be committed prior to the account
        // updates, since each account needs the most up-to-date storage
        // root
        storage_.commit_all_merged();
        accounts_.commit_all_merged();
        code_.commit_all_merged();
        current_txn_ = 0;
    }
};

MONAD_DB_NAMESPACE_END
