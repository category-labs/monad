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

#include <category/core/int.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct SignatureAndChain
{
    uint256_t r{};
    uint256_t s{};
    std::optional<uint256_t> chain_id{};
    uint8_t y_parity{};

    void from_v(uint256_t const &);

    /**
     * Returns true if the signature's s component is in the upper (malleated)
     * range forbidden by EIP-2.
     */
    constexpr bool has_upper_s() const
    {
        using namespace intx::literals;
        static constexpr auto secp256k1_order =
            0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141_u256;
        return s > secp256k1_order / 2;
    }

    friend bool
    operator==(SignatureAndChain const &, SignatureAndChain const &) = default;
};

static_assert(sizeof(SignatureAndChain) == 112);
static_assert(alignof(SignatureAndChain) == 8);

uint256_t get_v(SignatureAndChain const &) noexcept;

MONAD_NAMESPACE_END
