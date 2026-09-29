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
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/traits.hpp>

#include <functional>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
struct EvmcHost;

class State;

template <Traits traits>
vm::Result deploy_contract_code(State &, Address const &, vm::Result) noexcept;

template <Traits traits>
vm::Result
execute_create_message(EvmcHost<traits> *, State &, vm::Message const &);

template <Traits traits>
vm::Result
execute_call_message(EvmcHost<traits> *, State &, vm::Message const &);

MONAD_NAMESPACE_END
