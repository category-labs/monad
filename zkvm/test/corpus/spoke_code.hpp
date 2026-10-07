// Copyright (C) 2026 Category Labs, Inc.
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

// The spoke as an L2 genesis holds it: NamespaceSpoke's runtime code with its
// two immutables written in, which is what its constructor would have left at
// its address. See contracts/namespace_spoke_runtime.hpp.

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

class State;

namespace corpus
{
    class GenesisSink;

    /// Fixed genesis predeploy address: the access check needs the spoke
    /// before any transaction can deploy a contract.
    inline constexpr Address SPOKE_PREDEPLOY =
        0x0000000000000000000000000000000000001001_address;

    /// Vendored runtime behind the genesis access proxy. Presets use this
    /// address; the spoke scenario uses its CREATE-derived implementation.
    inline constexpr Address SPOKE_IMPLEMENTATION =
        0x0000000000000000000000000000000000001002_address;

    /// The code a CREATE of the spoke with these constructor arguments
    /// deploys.
    byte_string
    namespace_spoke_code(uint64_t namespace_chain_id, Address const &op);

    /// Test-only access proxy for the vendored NamespaceSpoke, which lacks
    /// canCall. Return ABI true for canCall; delegate other calls to impl so
    /// storage and logs remain at the spoke address. Not a protocol contract;
    /// replace with DomainSpoke when vendored. See CONFORMANCE.md.
    byte_string spoke_access_proxy(Address const &impl);

    /// Default domain genesis: access proxy at the spoke address, delegating
    /// to an unseeded SPOKE_IMPLEMENTATION. Message-producing scenarios must
    /// seed the implementation too. Both routes use nonce zero. No Ethereum
    /// action.
    void seed_spoke_access(State &);
    void seed_spoke_access(GenesisSink &);
}

MONAD_NAMESPACE_END
