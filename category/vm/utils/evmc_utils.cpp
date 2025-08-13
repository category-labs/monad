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

#include <category/vm/utils/evmc_utils.hpp>

#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <string>

namespace monad::vm::utils
{
    std::string hex_string(evmc::bytes32 const &x)
    {
        return evmc::hex({x.bytes, sizeof(x.bytes)});
    }

    std::string hex_string(evmc::address const &x)
    {
        return evmc::hex({x.bytes, sizeof(x.bytes)});
    }
}
