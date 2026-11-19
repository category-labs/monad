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

#pragma once

// Types of the recover_addresses interface declared in impl.hpp. They live in
// their own header because the zkvm build substitutes impl.hpp with its own
// implementation but includes this header unchanged, so host and zkvm share
// one definition.

#include <category/core/config.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

/// One element of a recover_addresses batch: the arguments of a single
/// recover_address call.
struct RecoverAddressInput
{
    uint8_t msg[32]; ///< message digest
    uint8_t sig[64]; ///< r || s, each 32 bytes big-endian
    uint8_t recid; ///< recovery id (y parity)
};

/// Result for one element of a recover_addresses batch. `address` is only
/// meaningful when `ok` is set.
struct RecoverAddressOutput
{
    uint8_t address[20];
    bool ok;
};

MONAD_NAMESPACE_END
