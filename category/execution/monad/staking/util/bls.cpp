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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/monad/staking/util/bls.hpp>

#include <algorithm>
#include <memory>

MONAD_STAKING_NAMESPACE_BEGIN

Address address_from_bls_key(byte_string_fixed<96> const &serialized_pubkey)
{
    Address eth_address{};
    // TODO: should we check if the 3 MSBs are zero?
    // https://github.com/supranational/blst?tab=readme-ov-file#serialization-format
    auto const hash = keccak256(to_byte_string_view(serialized_pubkey));
    std::copy_n(hash.bytes + 12, sizeof(Address), eth_address.bytes);
    return eth_address;
}

MONAD_STAKING_NAMESPACE_END
