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

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;
class State;

constexpr Address BLOCK_HISTORY_ADDRESS{
    0x0000F90827F1C53a10cb7A02335B175320002935_address};

constexpr uint64_t BLOCK_HISTORY_LENGTH{8191};

void deploy_block_hash_history_contract(State &);

void set_block_hash_history(State &, BlockHeader const &);

MONAD_NAMESPACE_END
