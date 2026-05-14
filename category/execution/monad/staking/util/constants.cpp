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

#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/monad/staking/util/constants.hpp>

MONAD_STAKING_NAMESPACE_BEGIN

// assertions go in cpp file so compile-time hash functions don't get
// re-executed in each translation unit.
static_assert(
    selector::REWARD == abi_encode_selector("syscallReward(address)"));

static_assert(selector::SNAPSHOT == abi_encode_selector("syscallSnapshot()"));

static_assert(
    selector::ON_EPOCH_CHANGE ==
    abi_encode_selector("syscallOnEpochChange(uint64)"));

MONAD_STAKING_NAMESPACE_END
