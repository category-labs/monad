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

#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/signature.hpp>

MONAD_NAMESPACE_BEGIN

void SignatureAndChain::from_v(uint256_t const &v)
{
    if (v == 28u) {
        y_parity = 1;
    }
    else if (v == 27u) {
        y_parity = 0;
    }
    else // chain_id has value
    {
        auto tmp = v - 35;
        if (tmp & 1u) {
            y_parity = 1;
            tmp ^= 1u;
        }
        chain_id = tmp >> 1;
    }
}

uint256_t get_v(SignatureAndChain const &sc) noexcept
{
    if (sc.chain_id.has_value()) {
        return (*sc.chain_id * 2u) + 35u + sc.y_parity;
    }
    return sc.y_parity ? 28u : 27u;
}

MONAD_NAMESPACE_END
