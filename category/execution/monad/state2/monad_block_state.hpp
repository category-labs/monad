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

// BlockState used during the slot-to-page migration. Holds a reference to
// a caller-provided page broker over Db2, alongside the base's slot broker
// over Db1. Every storage read goes through both brokers and asserts they
// agree - a sanity check that catches divergence between the two encodings
// while the migration is in flight. Non-storage reads (accounts, code) go
// through the base class's db_, which refers to Db1.
//
// The caller owns the PageStorageBroker and shares it with MonadCommitBuilder
// at commit time, so both consumers see the same cache of pages fetched
// during execution. It must outlive this MonadBlockState.
class MonadBlockState final : public BlockState
{
    PageStorageBroker &page_broker_;

public:
    MonadBlockState(Db &db1, PageStorageBroker &page_broker, vm::VM &);

protected:
    bytes32_t read_storage_from_broker(
        Address const &, Incarnation, bytes32_t const &key) override;
};

MONAD_NAMESPACE_END
