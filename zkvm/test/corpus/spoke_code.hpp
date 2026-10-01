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
    /// The code a CREATE of the spoke with these constructor arguments
    /// deploys.
    byte_string
    namespace_spoke_code(uint64_t namespace_chain_id, Address const &op);
}

MONAD_NAMESPACE_END
