#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <evmc/evmc.h>

#include <ankerl/unordered_dense.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

// YP 6.1
class AccountSubstate
{
    bool destructed_{false}; // A_s
    bool touched_{false}; // A_t
    bool accessed_{false}; // A_a
    std::vector<Receipt::Log> logs_{}; // A_l
    ankerl::unordered_dense::set<bytes32_t> accessed_storage_{}; // A_K

public:
    AccountSubstate() = default;
    AccountSubstate(AccountSubstate &&) = default;
    AccountSubstate(AccountSubstate const &) = default;
    AccountSubstate &operator=(AccountSubstate &&) = default;
    AccountSubstate &operator=(AccountSubstate const &) = default;

    // A_s
    bool is_destructed() const
    {
        return destructed_;
    }

    // A_t
    bool is_touched() const
    {
        return touched_;
    }

    // A_a
    bool is_accessed() const
    {
        return accessed_;
    }

    // A_l
    std::vector<Receipt::Log> const &get_logs() const
    {
        return logs_;
    }

    // A_K
    ankerl::unordered_dense::set<bytes32_t> const &get_accessed_storage() const
    {
        return accessed_storage_;
    }

    // A_s
    bool destruct()
    {
        bool const inserted = !destructed_;
        destructed_ = true;
        return inserted;
    }

    // A_t
    void touch()
    {
        touched_ = true;
    }

    // A_a
    bool access()
    {
        bool const inserted = !accessed_;
        accessed_ = true;
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    // A_l
    void append_log(Receipt::Log const &log)
    {
        logs_.emplace_back(log);
    }

    // A_K
    evmc_access_status access_storage(bytes32_t const &key)
    {
        bool const inserted = accessed_storage_.emplace(key).second;
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }
};

MONAD_NAMESPACE_END
