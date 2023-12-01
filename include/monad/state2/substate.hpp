#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>

#include <ankerl/unordered_dense.h>

#include <vector>

MONAD_NAMESPACE_BEGIN

// YP 6.1
struct Substate
{
    ankerl::unordered_dense::set<Address> destructed_{}; // A_s
    std::vector<Receipt::Log> logs_{}; // A_l
    ankerl::unordered_dense::set<Address> touched_{}; // A_t
    ankerl::unordered_dense::set<Address> accessed_{}; // A_a
    ankerl::unordered_dense::map<
        Address, ankerl::unordered_dense::set<bytes32_t>>
        accessed_storage_{}; // A_K
};

MONAD_NAMESPACE_END
