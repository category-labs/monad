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

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/vm/evm/chain.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <functional>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
struct EvmcHost;

class State;

template <Traits traits>
evmc::Result deploy_contract_code(
    State &, Address const &, evmc::Result, size_t max_code_size) noexcept;

template <Traits traits>
evmc::Result
create(EvmcHost<traits> *, State &, evmc_message const &, size_t max_code_size);

template <Traits traits>
evmc::Result call(
    EvmcHost<traits> *, State &, evmc_message const &,
    std::function<bool()> const &revert_transaction = [] { return false; });

MONAD_NAMESPACE_END
