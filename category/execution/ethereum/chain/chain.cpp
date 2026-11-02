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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
bool is_private_domain(ChainContext<traits> const &)
{
    return false;
}

EXPLICIT_EVM_TRAITS(is_private_domain);

template <Traits traits>
bool is_domain_system_relayer(ChainContext<traits> const &, Address const &)
{
    return false;
}

EXPLICIT_EVM_TRAITS(is_domain_system_relayer);

MONAD_NAMESPACE_END
