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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <functional>

MONAD_NAMESPACE_BEGIN

#ifdef MONAD_ZKVM_L2
/// What the access check forwards to the spoke, charged to the caller. Public
/// because it is a cost of the chain and not an implementation detail: a call
/// that cannot spare it is denied without being asked about, so the floor for
/// ANY call -- a transfer to an account with no code included -- is the
/// intrinsic cost plus this.
inline constexpr int64_t DOMAIN_ACCESS_GAS_STIPEND = 30'000;
#endif

template <Traits traits>
struct EvmcHost;

class State;

template <Traits traits>
evmc::Result
deploy_contract_code(State &, Address const &, evmc::Result) noexcept;

template <Traits traits>
evmc::Result
execute_create_message(EvmcHost<traits> *, State &, evmc_message const &);

template <Traits traits>
evmc::Result
execute_call_message(EvmcHost<traits> *, State &, evmc_message const &);

MONAD_NAMESPACE_END
