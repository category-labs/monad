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

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/monad/db/page_storage_broker.hpp>
#include <category/vm/vm.hpp>

MONAD_NAMESPACE_BEGIN

// BlockState that routes storage reads through a PageStorageBroker.
//
// Two modes of use:
//
//   1. Single-db replay (post-fork): the broker is over the only db, which
//      already holds page-encoded state. The caller passes only the broker;
//      the base class's db_ is the same db, used for account / code reads.
//
//   2. Dual-db migration: db1 is slot-encoded and the broker is over a
//      separate page-encoded db2. Each storage read goes through both the
//      base's slot read of db1 and the broker's page read of db2, asserting
//      they agree as a sanity check while the migration is in flight.
//
// The caller owns the PageStorageBroker and shares it with MonadCommitBuilder
// at commit time, so both consumers see the same cache of pages fetched
// during execution. It must outlive this MonadBlockState.
class MonadBlockState final : public BlockState
{
    PageStorageBroker &broker_;
    bool cross_check_;

public:
    // Single-db replay: page broker over the only db; no cross-check.
    MonadBlockState(PageStorageBroker &page_broker, vm::VM &);

    // Dual-db migration: cross-check db1 (base's slot read) vs db2 (broker).
    MonadBlockState(Db &db1, PageStorageBroker &page_broker, vm::VM &);

protected:
    bytes32_t read_storage_through_db(
        Address const &, Incarnation, bytes32_t const &key) override;
};

MONAD_NAMESPACE_END
