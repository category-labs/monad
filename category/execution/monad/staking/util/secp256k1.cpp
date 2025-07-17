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

#include <category/execution/monad/staking/util/secp256k1.hpp>

#include <algorithm>
#include <memory>

MONAD_STAKING_NAMESPACE_BEGIN

Address address_from_secpkey(byte_string_fixed<65> const &serialized_pubkey)
{
    Address eth_address{};
    MONAD_ASSERT(serialized_pubkey[0] == 4);
    byte_string_view view{serialized_pubkey.data() + 1, 64};
    auto const hash = keccak256(view);
    std::copy_n(hash.bytes + 12, sizeof(Address), eth_address.bytes);
    return eth_address;
}

secp256k1_context const *get_secp_context()
{
    thread_local std::unique_ptr<
        secp256k1_context,
        decltype(&secp256k1_context_destroy)> const
        secp_context(
            secp256k1_context_create(SECP256K1_CONTEXT_VERIFY),
            &secp256k1_context_destroy);
    return secp_context.get();
}

MONAD_STAKING_NAMESPACE_END
