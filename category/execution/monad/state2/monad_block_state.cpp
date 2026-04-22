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

MonadBlockState::MonadBlockState(PageStorageBroker &page_broker, vm::VM &vm)
    : BlockState{page_broker.db(), vm}
    , broker_{page_broker}
    , cross_check_{false}
{
}

MonadBlockState::MonadBlockState(
    Db &db1, PageStorageBroker &page_broker, vm::VM &vm)
    : BlockState{db1, vm}
    , broker_{page_broker}
    , cross_check_{true}
{
}

bytes32_t MonadBlockState::read_storage_through_db(
    Address const &address, Incarnation const incarnation, bytes32_t const &key)
{
    auto const page_res = broker_.read_storage_slot(address, incarnation, key);
    if (cross_check_) {
        // Dual-db: also read via the base's slot path against db1 and assert
        // both encodings agree. Both reads are required - the page read
        // populates the broker's cache that MonadCommitBuilder reuses at
        // commit time.
        auto const slot_res =
            BlockState::read_storage_through_db(address, incarnation, key);
        MONAD_ASSERT(slot_res == page_res);
    }
    return page_res;
}

MONAD_NAMESPACE_END
