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

namespace corpus
{
    /// Where this corpus puts the spoke. A FIXED address and not a
    /// CREATE-derived one: the access check asks the spoke before every call,
    /// so the spoke has to exist from genesis, before anything could have
    /// deployed it. It is also what the protocol describes DomainSpoke as -- a
    /// predeploy at a fixed address.
    inline constexpr Address SPOKE_PREDEPLOY =
        0x0000000000000000000000000000000000001001_address;

    /// Where the vendored runtime sits when a genesis seeds both halves: the
    /// spoke's own address holds the access proxy, and this holds what the
    /// proxy delegates to. Only the presets need it; the spoke scenario puts
    /// its implementation wherever its CREATE lands.
    inline constexpr Address SPOKE_IMPLEMENTATION =
        0x0000000000000000000000000000000000001002_address;

    /// The code a CREATE of the spoke with these constructor arguments
    /// deploys.
    byte_string
    namespace_spoke_code(uint64_t namespace_chain_id, Address const &op);

    /// A stand-in for DomainSpoke's access layer, and nothing more.
    ///
    /// The contract this tree vendors predates the rename and has no canCall,
    /// so against it the domain arm's access check denies every call and the
    /// corpus can exercise nothing. This answers canCall with the canonical
    /// ABI true and DELEGATECALLs everything else to `impl`, which holds the
    /// vendored runtime: delegatecall keeps `address()`, so storage still lives
    /// at the spoke and its logs are still emitted from it, which is what the
    /// anchor harvest reads.
    ///
    /// Eighty bytes of hand-written EVM, and a fixture -- not a contract the
    /// protocol has. It goes when DomainSpoke can be vendored, which needs
    /// solc; CONFORMANCE.md tracks that.
    byte_string spoke_access_proxy(Address const &impl);
}

MONAD_NAMESPACE_END
