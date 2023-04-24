#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/db/config.hpp>

#include <set>
#include <unordered_map>
#include <vector>

MONAD_DB_NAMESPACE_BEGIN

template <class TAccounts, class TAccountStorage>
struct State
{
    struct WorkingCopy
    {
        TAccounts::WorkingCopy accounts_;
        TAccountStorage storage_;
        std::vector<Receipt::Log> logs_{};
        unsigned int id_{};
        uint64_t _refund{};

        WorkingCopy(
            unsigned int i, TAccounts::WorkingCopy &&a,
            TAccountStorage &&s)
            : accounts_{a}
            , storage_{s}
            , id_{i}
        {
        }

        inline unsigned int id() const noexcept { return id_; }
        inline void create_contract(address_t const &a) noexcept
        {
            accounts_.create_contract(a);
        }

        [[nodiscard]] inline bool account_exists(address_t const &a) const
        {
            return accounts_.account_exists(a);
        }
        inline evmc_access_status access_account(address_t const &a) noexcept
        {
            return accounts_.access_account(a);
        }

        [[nodiscard]] inline bytes32_t
        get_balance(address_t const &a) const noexcept
        {
            return accounts_.get_balance(a);
        }

        inline void set_balance(address_t const &a, uint256_t const &b)
        {
            accounts_.set_balance(a, b);
        }

        [[nodiscard]] inline auto get_nonce(address_t const &a) const noexcept
        {
            return accounts_.get_nonce(a);
        }

        inline void set_nonce(address_t const &a, uint64_t nonce) noexcept
        {
            accounts_.set_nonce(a, nonce);
        }

        [[nodiscard]] inline bytes32_t
        get_code_hash(address_t const &a) const noexcept
        {
            return accounts_.get_code_hash(a);
        }

        inline void selfdestruct(address_t const &a, address_t const &b)
        {
            accounts_.selfdestruct(a, b);
        }

        inline void destruct_suicides() { accounts_.destruct_suicides(); }

        inline void destruct_touched_dead()
        {
            accounts_.destruct_touched_dead();
        }

        inline uint64_t total_selfdestructs() const noexcept
        {
            return accounts_.total_selfdestructs();
        }

        inline evmc_access_status
        access_storage(address_t const &a, bytes32_t const &key)
        {
            return storage_.access_storage(a, key);
        }

        [[nodiscard]] inline bytes32_t
        get_storage(address_t const &a, bytes32_t const &key) const noexcept
        {
            return storage_.get_storage(a, key);
        }

        [[nodiscard]] inline evmc_storage_status set_storage(
            address_t const &a, bytes32_t const &key, bytes32_t const &value)
        {
            return storage_.set_storage(a, key, value);
        }

        // Account contract accesses
        void set_code(address_t const &, byte_string const &) {}

        [[nodiscard]] size_t get_code_size(address_t const &) const noexcept
        {
            return 0u;
        }

        [[nodiscard]] size_t
        copy_code(address_t const &, size_t, uint8_t *, size_t) const noexcept
        {
            return 0u;
        }

        inline void revert()
        {
            accounts_.revert();
            storage_.revert();
        }

        // Logs
        void store_log(Receipt::Log &&l) { logs_.emplace_back(l); }

        std::vector<Receipt::Log> &logs() { return logs_; }

        uint64_t get_refund() const noexcept { return _refund; }
    };

    enum class MergeStatus
    {
        WILL_SUCCEED,
        TRY_LATER,
        COLLISION_DETECTED,
    };

    TAccounts &accounts_;
    TAccountStorage &storage_;
    unsigned int current_txn_{};

    State(TAccounts &a, TAccountStorage &s)
        : accounts_{a}
        , storage_{s}
    {
    }

    [[nodiscard]] bytes32_t get_block_hash(int64_t) { return {}; }

    inline unsigned int current_txn() { return current_txn_; }

    inline WorkingCopy get_working_copy(unsigned int id)
    {
        return WorkingCopy(
            id,
            accounts_.get_working_copy(),
            storage_.get_copy());
    }

    inline MergeStatus can_merge_changes(WorkingCopy const &c)
    {
        if (current_txn() != c.id()) { return MergeStatus::TRY_LATER; }

        if (accounts_.can_merge(c.accounts_) && storage_.can_merge(c.storage_))
        {
            return MergeStatus::WILL_SUCCEED;
        }
        return MergeStatus::COLLISION_DETECTED;
    }

    inline void merge_changes(WorkingCopy &c)
    {
        accounts_.merge_changes(c.accounts_);
        storage_.merge_touched(c.storage_);
        ++current_txn_;
    }
};

MONAD_DB_NAMESPACE_END
