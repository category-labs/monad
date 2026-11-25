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
#include <category/execution/ethereum/precompiles.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/message.hpp>
#include <category/vm/evm/result.hpp>
#include <category/vm/evm/traits.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
bool is_precompile(Address const &address)
{
    return is_eth_precompile<traits>(address);
}

EXPLICIT_MONAD_TRAITS(is_precompile);

template <Traits traits>
std::optional<vm::Result>
check_call_precompile(State &, CallTracerBase &, vm::Message const &msg, bool)
{
    return check_call_eth_precompile<traits>(msg);
}

EXPLICIT_MONAD_TRAITS(check_call_precompile);

MONAD_NAMESPACE_END
