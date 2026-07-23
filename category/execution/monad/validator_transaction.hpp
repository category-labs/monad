// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

#pragma once

#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

inline constexpr uint64_t VALIDATOR_TRANSACTION_BLOCK_GAS_LIMIT = 35'000'000;

inline bool is_validator_transaction(Transaction const &tx)
{
    return tx.type == TransactionType::validator;
}

inline bool is_well_formed_validator_transaction(Transaction const &tx)
{
    return is_validator_transaction(tx) && tx.max_fee_per_gas == 0 &&
           tx.max_priority_fee_per_gas == 0 && tx.value == 0 &&
           tx.to.has_value() && tx.authorization_list.empty();
}

MONAD_NAMESPACE_END
