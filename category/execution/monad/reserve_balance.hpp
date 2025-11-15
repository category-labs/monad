// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/evm/monad/revision.h>

#include <evmc/evmc.h>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct MonadChainContext;
class State;
struct Transaction;

bool revert_monad_transaction(
    monad_revision, evmc_revision, Address const &sender, Transaction const &,
    uint256_t const &base_fee_per_gas, uint64_t i, State &,
    MonadChainContext const &);

bool can_sender_dip_into_reserve(
    Address const &sender, uint64_t i, bool sender_is_delegated,
    MonadChainContext const &);

uint256_t get_max_reserve(monad_revision, Address const &);

MONAD_NAMESPACE_END
