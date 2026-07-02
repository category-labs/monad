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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct EcdsaSignature;

/// Recovers the Ethereum address that signed `encoding` with the given ECDSA
/// signature. Rejects malformed signatures up-front (y_parity > 1, malleable
/// s); returns nullopt if ECDSA recovery fails.
///
/// Kept in its own TU so the silkpre / secp256k1 dependency is confined to a
/// single source file, and can be substituted on platforms that supply
/// ecrecover via syscall.
std::optional<Address>
recover_address(EcdsaSignature const &, byte_string_view encoding);

MONAD_NAMESPACE_END
