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

#pragma once

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>

#include <evmc/evmc.h>

#include <cstdint>
#include <optional>
#include <span>

namespace monad::vm::evm
{
    byte_string_view delegation_indicator_prefix();

    bool is_delegated(std::span<uint8_t const> code);

    // Return the EIP-7702 delegate for exactly 0xEF0100 + a 20-byte address.
    std::optional<Address> designation_of(std::span<uint8_t const> code);

#if defined(MONAD_ZKVM_ZISK)
    // designation_of's address where it lies in the code, or null: no
    // optional to fill and return through memory, so the methods that pass
    // the delegate on are jumps.
    Address const *delegate_in(std::span<uint8_t const> code);

    Address const *resolve_delegation(
        evmc_host_interface const *, evmc_host_context *, Address const &);
#else
    std::optional<Address> resolve_delegation(
        evmc_host_interface const *, evmc_host_context *, Address const &);
#endif
}
