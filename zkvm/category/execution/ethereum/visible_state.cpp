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

// zkVM shadow of category/execution/ethereum/visible_state.cpp: a node the
// witness does not carry (a Digest on the lookup path) is not visible. Only
// the pre-state trie is consulted; the two callers never need a value written
// earlier in the block that the pre-state cannot show (the EIP-2935 system
// call's target slot is in every witness, and an account created in-block has
// an insertable, hence visible, path).

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <zkvm/category/execution/ethereum/visible_state.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

PartialTrieDb *g_db = nullptr;

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

void set_visible_state_db(PartialTrieDb &db)
{
    g_db = &db;
}

bool is_account_in_partial_state(Address const &address)
{
    MONAD_ASSERT(g_db != nullptr);
    return g_db->account_in_partial_state(address);
}

bool is_storage_in_partial_state(Address const &address, bytes32_t const &key)
{
    MONAD_ASSERT(g_db != nullptr);
    return g_db->storage_in_partial_state(address, key);
}

MONAD_NAMESPACE_END
