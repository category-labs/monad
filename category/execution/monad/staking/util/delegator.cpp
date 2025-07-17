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

#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/staking/util/delegator.hpp>

#include <intx/intx.hpp>

MONAD_STAKING_NAMESPACE_BEGIN

Delegator::Delegator(State &state, Address const &address, bytes32_t const key)
    : state_{state}
    , address_{address}
    , key_{intx::be::load<uint256_t>(key)}
{
}

MONAD_STAKING_NAMESPACE_END
