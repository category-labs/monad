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
#include <category/core/fiber/priority_pool.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
class BlockState;
struct CallTracerBase;
struct Chain;
struct Transaction;

template <Traits traits>
Result<std::vector<Receipt>> state_after_transactions(
    Chain const &, BlockHeader const &, std::vector<Transaction> const &,
    std::vector<Address> const &senders,
    std::vector<std::vector<std::optional<Address>>> const &authorities,
    BlockState &, BlockHashBuffer const &, fiber::PriorityPool &,
    std::vector<std::unique_ptr<trace::StateTracer>> &state_tracers);

MONAD_NAMESPACE_END
