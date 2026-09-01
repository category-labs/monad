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

#include <bit>

// The scalar byte-order primitive, behind a name of our own so that the zkVM
// guest can substitute an implementation which does not call out to libgcc —
// see zkvm/category/core/runtime/bit.hpp, which open-codes the 4- and 8-byte
// cases for riscv64ima, a target with no rev8 instruction.
//
// Callers outside this directory want monad::bswap (category/core/int.hpp): it
// is the canonical entry point and also covers uint256_t and uint128_t.
namespace monad::bit
{
    using std::byteswap;
}
