#pragma once

#include "monad/state/state.hpp"
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/state/config.hpp>
#include <monad/state/datum.hpp>
#include <monad/state/state_changes.hpp>

#include <algorithm>
#include <cassert>
#include <unordered_map>

MONAD_STATE_NAMESPACE_BEGIN

template <class TAccountDB>
struct AccountState
{
    using diff_t = diff<std::optional<Account>>;
    using change_set_t = std::unordered_map<address_t, diff_t>;

    struct WorkingCopy;

    // TODO Irrevocable change separated out to avoid reversion
    TAccountDB &db_;
    change_set_t merged_{};

    AccountState(TAccountDB &a)
        : db_{a}
    {
    }

    /**
     * Apply a reward to an account, and create that account if new
     *
     * NOTE: There are different rules for mining rewards - accounts can spring
     * into existance without first being created. This specialized function
     * works on the parent state object and inserts the rewards directly into
     * the merge set.
     */
    void apply_reward(address_t const &a, uint256_t const &r)
    {
        auto account_before = get_committed_storage(a);

        if (!account_before.has_value()) {
            merged_.emplace(a, diff_t{account_before, Account{}});
        } else if (!merged_.contains(a)) {
            merged_.emplace(a, diff_t{account_before, account_before});
        }

        merged_.at(a).updated.value().balance += r;
    }

    [[nodiscard]] std::optional<Account>
    get_committed_storage(address_t const &a) const
    {
        if (merged_.contains(a)) {
            return merged_.at(a).updated;
        }
        return db_.query(a);
    }

    // EVMC Host Interface
    [[nodiscard]] bool account_exists(address_t const &a) const noexcept
    {
        if (merged_.contains(a)) {
            return merged_.at(a).updated.has_value();
        }
        return db_.contains(a);
    }

    // EVMC Host Interface
    [[nodiscard]] evmc_access_status access_account(address_t const &) noexcept
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

    [[nodiscard]] bool can_merge(WorkingCopy const &diffs) const noexcept
    {
        return std::ranges::all_of(diffs.changed_, [&](auto const &p) {
            return get_committed_storage(p.first) == p.second.orig;
        });
    }

    void merge_changes(WorkingCopy &diffs)
    {
        assert(can_merge(diffs));

        for (auto &[a, A] : diffs.changed_) {
            if (merged_.contains(a)) {
                merged_.at(a).updated = A.updated;
            }
            else {
                merged_.emplace(a, A);
            }
        }
    }

    [[nodiscard]] bool can_commit() const noexcept
    {
        return std::ranges::all_of(merged_, [&](auto const &p) {
            if (p.second.orig.has_value()) {
                return db_.contains(p.first) &&
                       p.second.orig == db_.at(p.first);
            }
            return not db_.contains(p.first);
        });
    }

    void commit_all_merged()
    {
        assert(can_commit());

        StateChanges sc;
        for (auto const &[addr, diff] : merged_) {
            sc.account_changes.emplace_back(addr, diff.updated);
        }

        db_.commit(sc);
        merged_.clear();
    }

    [[nodiscard]] bytes32_t get_state_hash() const { return db_.root_hash(); }
};

template <typename TAccountDB>
struct AccountState<TAccountDB>::WorkingCopy : public AccountState<TAccountDB>
{
    change_set_t changed_{};
    uint64_t total_selfdestructs_{};

    // EVMC Host Interface
    [[nodiscard]] bool account_exists(address_t const &a) const noexcept
    {
        if (changed_.contains(a)) {
            if (changed_.at(a).updated.has_value()) {
                return true;
            }
            return false;
        }
        return AccountState::account_exists(a);
    }

    void create_account(address_t const &a)
    {
        auto const [_, inserted] =
            changed_.emplace(a, diff_t{get_committed_storage(a), Account{}});
        MONAD_DEBUG_ASSERT(inserted);
    }

    // EVMC Host Interface
    evmc_access_status access_account(address_t const &a)
    {
        MONAD_DEBUG_ASSERT(account_exists(a));
        if (changed_.contains(a)) {
            return EVMC_ACCESS_WARM;
        }
        changed_.emplace(
            a, diff_t{get_committed_storage(a), *get_committed_storage(a)});
        return EVMC_ACCESS_COLD;
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t get_balance(address_t const &a) const noexcept
    {
        return intx::be::store<bytes32_t>(
            changed_.at(a).updated.value_or(Account{}).balance);
    }

    void set_balance(address_t const &address, uint256_t new_balance) noexcept
    {
        changed_.at(address).updated.value().balance = new_balance;
    }

    [[nodiscard]] uint64_t get_nonce(address_t const &address) const noexcept
    {
        return changed_.at(address).updated.value_or(Account{}).nonce;
    }

    void set_nonce(address_t const &address, uint64_t nonce) noexcept
    {
        changed_.at(address).updated.value().nonce = nonce;
    }

    // EVMC Host Interface
    [[nodiscard]] bytes32_t
    get_code_hash(address_t const &address) const noexcept
    {
        return changed_.at(address).updated.value_or(Account{}).code_hash;
    }

    void set_code_hash(address_t const &address, bytes32_t const &b) noexcept
    {
        MONAD_DEBUG_ASSERT(changed_.at(address).updated.has_value());
        changed_.at(address).updated.value().code_hash = b;
    }

    [[nodiscard]] bool
    selfdestruct(address_t const &a, address_t const &beneficiary) noexcept
    {
        if (changed_.at(a).updated) {
            changed_.at(beneficiary).updated.value().balance +=
                changed_.at(a).updated.value().balance;
            changed_.at(a).updated.reset();
            ++total_selfdestructs_;
            return true;
        }
        return false;
    }

    void destruct_suicides() const noexcept {}

    void destruct_touched_dead() noexcept
    {
        for (auto &i : changed_) {
            if (i.second.updated.has_value() &&
                i.second.updated.value() == Account{}) {
                i.second.updated.reset();
            }
        }
    }

    [[nodiscard]] uint64_t total_selfdestructs() const noexcept
    {
        return total_selfdestructs_;
    }

    void revert() noexcept { changed_.clear(); }
};

MONAD_STATE_NAMESPACE_END
