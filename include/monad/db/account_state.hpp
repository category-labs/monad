#pragma once

#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <monad/db/config.hpp>

#include <unordered_map>
#include <vector>

MONAD_DB_NAMESPACE_BEGIN

template<class TAccounts>
struct Accounts
{
    TAccounts &accounts_;

    Accounts(TAccounts &a) : accounts_{a} {}

    //struct InnerStorage
    //{
    std::unordered_map<address_t, Account> touched_accounts_{};
    std::vector<address_t> deleted_accounts_{};
    std::vector<address_t> created_accounts_{};
    std::vector<address_t> touched_dead_{};

    void create_contract(address_t const &a) noexcept
    {
        created_accounts_.push_back(a);
        touched_accounts_.emplace(std::make_pair(a, Account{}));
    }

    [[nodiscard]] bool account_exists(address_t const &a) const
    {
        return accounts_.contains(a) || std::find(
                                            std::cbegin(created_accounts_),
                                            std::cend(created_accounts_),
                                            a) != std::cend(created_accounts_);
    }

    evmc_access_status access_account(address_t const &a) noexcept
    {
        if(touched_accounts_.contains(a)) {
            return EVMC_ACCESS_WARM;
        }
        touched_accounts_[a] = accounts_.at(a);
        return EVMC_ACCESS_COLD;
    }

    [[nodiscard]] bytes32_t get_balance(address_t const &a) const noexcept
    {
        return intx::be::store<bytes32_t>(touched_accounts_.at(a).balance);
    }

    void set_balance(address_t const &address, uint256_t new_balance)
    {
        touched_accounts_.at(address).balance = new_balance;
    }

    [[nodiscard]] auto get_nonce(address_t const &address) const noexcept
    {
        return touched_accounts_.at(address).nonce;
    }

    void set_nonce(address_t const &address, uint64_t nonce) noexcept
    {
        touched_accounts_.at(address).nonce = nonce;
    }

    [[nodiscard]] bytes32_t
    get_code_hash(address_t const &address) const noexcept
    {
        return accounts_.at(address).code_hash;
    }

    void selfdestruct(address_t const &a, address_t const &beneficiary)
    {
        deleted_accounts_.push_back(a);
        touched_accounts_.at(beneficiary).balance +=
            touched_accounts_.at(a).balance;
        touched_accounts_.at(a).balance = 0u;
    }

    void destruct_suicides()
    {
        for (auto const &a : deleted_accounts_) {
            touched_accounts_.erase(a);
        }
    }

    void destruct_touched_dead()
    {
        for (auto const &i : touched_accounts_) {
            if (i.second.balance == 0 && i.second.nonce == 0 &&
                i.second.code_hash == NULL_HASH) {
                touched_dead_.push_back(i.first);
            }
        }
        for (auto const &i : touched_dead_) {
            touched_accounts_.erase(i);
        }
    }

    uint64_t total_selfdestructs() const noexcept
    {
        return deleted_accounts_.size();
    }

    void commit()
    {
        for (auto const &i : touched_accounts_) {
            accounts_[i.first] = i.second;
        }
        for (auto const &a : deleted_accounts_) {
            accounts_.erase(a);
        }
        for (auto const &d : touched_dead_) {
            accounts_.erase(d);
        }
        revert();
    };

    void revert()
    {
        created_accounts_.clear();
        deleted_accounts_.clear();
        touched_dead_.clear();
        touched_accounts_.clear();
    }

    inline bool apply_state(Accounts const &) { return true; }

    inline Accounts get_copy() { return InMemoryAccountState(*this); }
};

MONAD_DB_NAMESPACE_END
