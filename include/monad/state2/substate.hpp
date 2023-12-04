#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <evmc/evmc.h>

#include <ankerl/unordered_dense.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

// YP 6.1
class Substate
{
    ankerl::unordered_dense::set<Address> destructed_{}; // A_s
    std::vector<Receipt::Log> logs_{}; // A_l
    ankerl::unordered_dense::set<Address> touched_{}; // A_t
    ankerl::unordered_dense::set<Address> accessed_{}; // A_a
    ankerl::unordered_dense::map<
        Address, ankerl::unordered_dense::set<bytes32_t>>
        accessed_storage_{}; // A_K

protected:
    auto const &destructed() const
    {
        return destructed_;
    }

    auto const &touched() const
    {
        return touched_;
    }

public:
    Substate() = default;
    Substate(Substate &&) = default;
    Substate(Substate const &) = default;
    Substate &operator=(Substate &&) = default;
    Substate &operator=(Substate const &) = default;

    auto const &logs() const
    {
        return logs_;
    }

    bool is_touched(Address const &address) const
    {
        return touched_.contains(address);
    }

    bool selfdestruct(Address const &address)
    {
        bool const inserted = destructed_.emplace(address).second;
        return inserted;
    }

    void store_log(Receipt::Log const &log)
    {
        logs_.emplace_back(log);
    }

    void touch(Address const &address)
    {
        touched_.insert(address);
    }

    evmc_access_status access_account(Address const &address)
    {
        bool const inserted = accessed_.emplace(address).second;
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }

    evmc_access_status
    access_storage(Address const &address, bytes32_t const &key)
    {
        bool const inserted = accessed_storage_[address].emplace(key).second;
        if (inserted) {
            return EVMC_ACCESS_COLD;
        }
        return EVMC_ACCESS_WARM;
    }
};

MONAD_NAMESPACE_END
