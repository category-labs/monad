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

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/ecrecover/types.hpp>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

/// Wrapper around the implementation kept in its own TU so the silkpre /
/// secp256k1 dependency is confined to a single source file, and can be
/// substituted on platforms that supply ecrecover via syscall.
bool recover_address(
    std::span<uint8_t, 20> const out, std::span<uint8_t const, 32> const msg,
    std::span<uint8_t const, 64> const sig, uint8_t recid);

/// Batched recover_address: `out[i]` receives the result for `in[i]`, which
/// must be exactly what recover_address would return for it. Elements succeed
/// or fail independently. `in` and `out` must have the same size and may be
/// of any size, including zero. An implementation is free to process the
/// elements in parallel lanes and in any order.
void recover_addresses(
    std::span<RecoverAddressInput const> in,
    std::span<RecoverAddressOutput> out);

MONAD_NAMESPACE_END
