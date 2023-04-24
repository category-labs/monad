#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/db/config.hpp>
#include <monad/db/datum.hpp>

#include <unordered_map>

MONAD_DB_NAMESPACE_BEGIN

template <class TAccounts>
struct Accounts
{
    struct ChangeSet
    {
        std::unordered_map<address_t, diff<Account>> accounts_{};

        void inline clear() { accounts_.clear(); }
    };

    struct WorkingCopy : public Accounts
    {
        ChangeSet changed_;
        uint64_t total_selfdestructs_{};

        [[nodiscard]] bool account_exists(address_t const &a) const
        {
            if (changed_.accounts_.contains(a)) {
                if (changed_.accounts_.at(a).updated.has_value()) {
                    return true;
                }
                return false;
            }
            return Accounts::account_exists(a);
        }

        void create_contract(address_t const &a) noexcept
        {
            auto const [_, inserted] =
                changed_.accounts_.emplace(std::make_pair(
                    a,
                    diff<Account>{get_committed_storage(a), Account{}}));
            MONAD_ASSERT(inserted);
        }

        evmc_access_status access_account(address_t const &a) noexcept
        {
            if (changed_.accounts_.contains(a)) {
                return EVMC_ACCESS_WARM;
            }
            changed_.accounts_.insert(std::make_pair(
                a,
                diff<Account>{
                    get_committed_storage(a), *get_committed_storage(a)}));
            return EVMC_ACCESS_COLD;
        }

        [[nodiscard]] bytes32_t get_balance(address_t const &a) const noexcept
        {
            return intx::be::store<bytes32_t>(
                changed_.accounts_.at(a).updated.value_or(Account{}).balance);
        }

        void set_balance(address_t const &address, uint256_t new_balance)
        {
            changed_.accounts_.at(address).updated.value().balance =
                new_balance;
        }

        [[nodiscard]] auto get_nonce(address_t const &address) const noexcept
        {
            return changed_.accounts_.at(address).updated.value_or(Account{}).nonce;
        }

        void set_nonce(address_t const &address, uint64_t nonce) noexcept
        {
            changed_.accounts_.at(address).updated.value().nonce = nonce;
        }

        [[nodiscard]] bytes32_t
        get_code_hash(address_t const &address) const noexcept
        {
            return changed_.accounts_.at(address).updated.value_or(Account{}).code_hash;
        }

        void selfdestruct(address_t const &a, address_t const &beneficiary)
        {
            changed_.accounts_.at(beneficiary).updated.value().balance +=
                changed_.accounts_.at(a).updated.value().balance;
            changed_.accounts_.at(a).updated.reset();
            ++total_selfdestructs_;
        }

        void destruct_suicides() {}

        void destruct_touched_dead()
        {
            for (auto &i : changed_.accounts_) {
                if (i.second.updated.has_value() && 
                    i.second.updated.value().balance == 0 &&
                    i.second.updated.value().nonce == 0 &&
                    i.second.updated.value().code_hash == NULL_HASH) {
                    i.second.updated.reset();
                }
            }
        }

        uint64_t total_selfdestructs() const noexcept
        {
            return total_selfdestructs_;
        }

        void revert() { changed_.clear(); }
    };

    // TODO Irrevocable change separated out to avoid reversion
    TAccounts &accounts_;
    ChangeSet merged_{};

    Accounts(TAccounts &a)
        : accounts_{a}
    {
    }

    inline bool committed_storage_contains(address_t const &a)
    {
        if (merged_.accounts_.contains(a)) {
            if (merged_.accounts_.at(a).updated.has_value()) {
                return true;
            }
            return false;
        }
        if (accounts_.contains(a)) {
            return true;
        }
        return false;
    }

    inline std::optional<Account>
    get_committed_storage(address_t const &a) const
    {
        if (merged_.accounts_.contains(a)) {
            return merged_.accounts_.at(a).updated;
        }
        if (accounts_.contains(a)) {
            return {accounts_.at(a)};
        }
        return {};
    }

    // EVMC Host Interface
    [[nodiscard]] bool account_exists(address_t const &a) const
    {
        if (merged_.accounts_.contains(a)) {
            if (merged_.accounts_.at(a).updated.has_value()) {
                return true;
            }
            return false;
        }
        return accounts_.contains(a);
    }

    // EVMC Host Interface
    evmc_access_status access_account(address_t const &) noexcept
    {
        return EVMC_ACCESS_COLD;
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_balance(address_t const &a) const noexcept
    {
        return intx::be::store<bytes32_t>(
            get_committed_storage(a).value_or(Account{}).balance);
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_code_hash(address_t const &a) const noexcept
    {
        return get_committed_storage(a).value_or(Account{}).code_hash;
    }

    inline WorkingCopy get_working_copy()
    {
        WorkingCopy a(*this);
        return a;
    }

    inline bool can_merge(WorkingCopy const &diffs)
    {
        for (auto const &[a, acct] : diffs.changed_.accounts_) {
            if (acct.orig.has_value()) {
                if (!committed_storage_contains(a)) {
                    return false;
                }
                if (get_committed_storage(a) != acct.orig) {
                    return false;
                }
            }
            else {
                if (committed_storage_contains(a)) {
                    return false;
                }
            }
        }

        return true;
    }

    inline void merge_changes(WorkingCopy &diffs)
    {
        for (auto &[a, A] : diffs.changed_.accounts_) {
            if (merged_.accounts_.contains(a)) {
                merged_.accounts_.at(a).updated = A.updated;
            }
            else {
                merged_.accounts_.insert({a, A});
            }
        }
    }

    inline bool can_commit()
    {
        for (auto const &[a, A] : merged_.accounts_) {
            if (A.orig.has_value()) {
                if (!accounts_.contains(a)) {
                    return false;
                } else if (A.orig.value() != accounts_.at(a)) {
                    return false;
                }
            }
            else if (accounts_.contains(a)) {
                return false;
            }
        }
        return true;
    }

    inline void commit_all_merged()
    {
        for (auto const &[a, A] : merged_.accounts_) {
            if (A.orig.has_value()) {
                if (A.updated.has_value()) {
                    accounts_[a] = A.updated.value();
                }
                else {
                    accounts_.erase(a);
                }
            }
            else {
                accounts_.emplace(a, A.updated.value());
            }
        }
        merged_.clear();
    }
};

MONAD_DB_NAMESPACE_END
