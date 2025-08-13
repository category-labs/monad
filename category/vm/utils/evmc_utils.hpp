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

#include <evmc/evmc.hpp>

namespace monad::vm::utils
{
    inline std::size_t hash32_hash(evmc::bytes32 const &hash32)
    {
        static_assert(sizeof(std::size_t) >= sizeof(uint64_t));
        std::uint64_t result;
        std::memcpy(&result, hash32.bytes, 8);
        std::uint64_t tmp;
        std::memcpy(&tmp, hash32.bytes + 8, 8);
        result ^= tmp;
        std::memcpy(&tmp, hash32.bytes + 16, 8);
        result ^= tmp;
        std::memcpy(&tmp, hash32.bytes + 24, 8);
        result ^= tmp;
        return result;
    }

    struct Hash32Hash
    {
        std::size_t operator()(evmc::bytes32 const &hash32) const
        {
            return hash32_hash(hash32);
        }
    };

    struct Bytes32Equal
    {
        bool operator()(evmc::bytes32 const &x, evmc::bytes32 const &y) const
        {
            return x == y;
        }
    };

    struct Hash32Compare
    {
        std::size_t hash(evmc::bytes32 const &hash32) const
        {
            return hash32_hash(hash32);
        }

        bool equal(evmc::bytes32 const &x, evmc::bytes32 const &y) const
        {
            return x == y;
        }
    };

    std::string hex_string(evmc::bytes32 const &);
    std::string hex_string(evmc::address const &);
}
