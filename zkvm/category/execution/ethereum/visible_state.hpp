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

// zkVM shadow of category/execution/ethereum/visible_state.hpp: the host
// defines these inline as `true`; the RISC-V guest, where this directory
// precedes the root on the include path, sees these declarations instead and
// the definitions in visible_state.cpp next to this header answer from the
// witness-backed DB. The x86 test runner recompiles the two host TUs that
// consult these predicates against this header (zkvm/guest/CMakeLists.txt),
// so it exercises the same fallbacks natively.

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>

MONAD_NAMESPACE_BEGIN

bool is_account_in_partial_state(Address const &);
bool is_storage_in_partial_state(Address const &, bytes32_t const &key);

// Registered once per run, before the block executes.
void set_visible_state_db(PartialTrieDb &);

MONAD_NAMESPACE_END
