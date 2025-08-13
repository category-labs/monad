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

MONAD_NAMESPACE_BEGIN

// EIP-4895
struct Withdrawal
{
    uint64_t index{0};
    uint64_t validator_index{};
    uint64_t amount{};
    Address recipient{};

    friend bool operator==(Withdrawal const &, Withdrawal const &) = default;
};

static_assert(sizeof(Withdrawal) == 48);
static_assert(alignof(Withdrawal) == 8);

MONAD_NAMESPACE_END
