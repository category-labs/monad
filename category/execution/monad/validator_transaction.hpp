// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

#pragma once

#include <category/execution/ethereum/core/transaction.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

inline constexpr uint64_t VALIDATOR_TRANSACTION_BLOCK_GAS_LIMIT = 35'000'000;

inline bool is_validator_transaction(
    Transaction const &tx, std::optional<Address> const &validator_contract)
{
    return tx.to == validator_contract && validator_contract.has_value();
}

inline bool is_well_formed_validator_transaction(
    Transaction const &tx, std::optional<Address> const &validator_contract)
{
    return is_validator_transaction(tx, validator_contract) &&
           tx.type == TransactionType::eip1559 && tx.value == 0 &&
           tx.authorization_list.empty();
}

MONAD_NAMESPACE_END
