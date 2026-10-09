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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN

// Whether the backing state can show an account or a storage slot at all.
// Always true for a node with full state, and inline so the check folds away
// in the regular client. The zkVM guest shadows this header
// (zkvm/category/execution/ethereum/visible_state.hpp) with declarations the
// guest defines to answer false when its witness lacks the node, so the
// callers that either have another verified source (BLOCKHASH from the header
// chain) or need no load at all (State::access_account: an account the witness
// lacks was never loaded, hence is cold) can skip the read instead of aborting
// on an incomplete witness.
[[gnu::always_inline]] inline bool is_account_in_partial_state(Address const &)
{
    return true;
}

[[gnu::always_inline]] inline bool
is_storage_in_partial_state(Address const &, bytes32_t const &)
{
    return true;
}

MONAD_NAMESPACE_END
