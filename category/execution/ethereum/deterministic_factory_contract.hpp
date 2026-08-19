// Copyright (C) 2025-26 Category Labs, Inc.
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

MONAD_NAMESPACE_BEGIN

class State;

constexpr Address DETERMINISTIC_FACTORY_ADDRESS{
    0x4e59b44847b379578588920cA78FbF26c0B4956C_address};

template <Traits traits>
void deploy_deterministic_factory_contract(State &);

MONAD_NAMESPACE_END
