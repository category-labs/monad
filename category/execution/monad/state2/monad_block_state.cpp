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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/state2/monad_block_state.hpp>
#include <category/vm/vm.hpp>

MONAD_NAMESPACE_BEGIN

MonadBlockState::MonadBlockState(
    Db &db1, PageStorageBroker &page_broker, vm::VM &vm)
    : BlockState{db1, vm}
    , page_broker_{page_broker}
{
}

bytes32_t MonadBlockState::read_storage_from_broker(
    Address const &address, Incarnation const incarnation,
    bytes32_t const &key)
{
    // Read from both Db1 (via the base's slot broker) and Db2 (via the page
    // broker) and assert they agree. Both reads are required: they
    // populate each broker's cache with the pre-commit state that the
    // corresponding CommitBuilder will read back to merge deltas.
    auto const slot_res =
        BlockState::read_storage_from_broker(address, incarnation, key);
    auto const page_res =
        page_broker_.read_storage_slot(address, incarnation, key);
    MONAD_ASSERT(slot_res == page_res);
    return slot_res;
}

MONAD_NAMESPACE_END
