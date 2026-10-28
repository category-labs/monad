// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#pragma once

#include <category/core/config.hpp>
#include <category/core/int.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

// Price of one unit of domain gas, in wei of the L1 native token. Mirrors
// DomainHub.DOMAIN_GAS_PRICE: the fee a hub call attaches buys
// `fee / DOMAIN_GAS_PRICE` gas of domain execution.
inline constexpr uint256_t DOMAIN_GAS_PRICE{50'000'000'000};

// Gas a fee buys, capped at the gas limit of the enclosing L1 block.
inline uint64_t
purchased_domain_gas(uint256_t const &fee, uint64_t const block_gas_limit)
{
    uint256_t const gas = fee / DOMAIN_GAS_PRICE;
    return gas < uint256_t{block_gas_limit} ? static_cast<uint64_t>(gas)
                                            : block_gas_limit;
}

MONAD_NAMESPACE_END
