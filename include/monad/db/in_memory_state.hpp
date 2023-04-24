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

template< class TAccounts, class TAccountStorage>
struct State
{
    TAccounts accounts_{};
    TAccountStorage account_storage_{};

    uint64_t _refund{};
    int current_txn_{};
    bool _applied_state{};
    std::vector<Receipt::Log> logs_{};

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

    [[nodiscard]] inline bytes32_t get_balance(address_t const &a) const noexcept
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

    inline void destruct_suicides()
    {
        accounts_.destruct_suicides();
    }

    inline void destruct_touched_dead()
    {
        accounts_.destruct_touched_dead();
    }

    inline uint64_t total_selfdestructs() const noexcept
    {
        return accounts_.total_selfdestructs();
    }

    inline void commit()
    {
        accounts_.commit();
        account_storage_.commit();
    };

    inline void revert()
    {
        accounts_.revert();
        account_storage_.revert();
    }

    [[nodiscard]] inline bytes32_t
    get_storage(address_t const &a, bytes32_t const &key) const noexcept
    {
        return account_storage_.get_storage(a, key);
    }

    [[nodiscard]] inline evmc_storage_status set_storage(
        address_t const &a, bytes32_t const &key, bytes32_t const &value)
    {
        return account_storage_.set_storage(a, key, value);
    }

    inline evmc_access_status
    access_storage(address_t const &a, bytes32_t const &key)
    {
        return account_storage_.access_storage(a, key);
    }

    // Account contract accesses
    [[nodiscard]] size_t get_code_size(address_t const &) const noexcept
    {
        return 0u;
    }

    [[nodiscard]] size_t
    copy_code(address_t const &, size_t, uint8_t *, size_t) const noexcept
    {
        return 0u;
    }

    void set_code(address_t const &, byte_string const &) {}

    [[nodiscard]] bytes32_t get_block_hash(int64_t) { return {}; }

    uint64_t get_refund() const noexcept { return _refund; }

    inline int current_txn() { return current_txn_; }

    // Logs
    void store_log(Receipt::Log &&l) { logs_.emplace_back(l); }

    std::vector<Receipt::Log> &logs() { return logs_; }

    inline bool apply_state(TAccounts const &) { return _applied_state; }
    inline bool apply_storage(TAccountStorage const &) { return _applied_state; }

    //inline InMemoryState get_account_state() { return InMemoryState(*this); }
    //inline InMemoryState get_copy() { return InMemoryState(*this); }
};

MONAD_DB_NAMESPACE_END
