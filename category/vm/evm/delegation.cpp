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

#include <category/core/byte_string.hpp>
#include <category/vm/evm/delegation.hpp>

#include <algorithm>
#include <cstdint>
#include <span>

namespace monad::vm::evm
{
    byte_string_view delegation_indicator_prefix()
    {
        return {
            delegation_indicator_prefix_bytes.data(),
            delegation_indicator_prefix_bytes.size()};
    }

    bool is_delegated(std::span<uint8_t const> const code)
    {
        if (code.size() != delegation_indicator_size) {
            return false;
        }

        auto const prefix = delegation_indicator_prefix();
        return std::equal(prefix.begin(), prefix.end(), code.begin());
    }
}
