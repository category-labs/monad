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
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/deterministic_factory_contract.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/vm/evm/explicit_traits.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

byte_string const FACTORY_CODE =
    from_hex("0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
             "fe03601600081602082378035828234f58015156039578182fd5b808252505050"
             "6014600cf3")
        .value();

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

// EIP-7997
template <Traits traits>
void deploy_deterministic_factory_contract(State &state)
{
    if constexpr (!traits::eip_7997_active()) {
        return;
    }

    if (MONAD_UNLIKELY(
            !state.account_has_code_or_nonce(DETERMINISTIC_FACTORY_ADDRESS))) {
        state.create_contract(DETERMINISTIC_FACTORY_ADDRESS);
        state.set_code(DETERMINISTIC_FACTORY_ADDRESS, FACTORY_CODE);
        state.set_nonce(DETERMINISTIC_FACTORY_ADDRESS, 1);
    }
}

EXPLICIT_TRAITS(deploy_deterministic_factory_contract);

MONAD_NAMESPACE_END
