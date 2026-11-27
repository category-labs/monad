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
#include <category/execution/ethereum/state3/state.hpp>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

// EIP-4788: write the parent beacon block root into the beacon roots
// contract's ring buffer, if the contract exists. The header must carry
// parent_beacon_block_root.
void set_beacon_root(State &, BlockHeader const &);

MONAD_NAMESPACE_END
