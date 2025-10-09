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
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/fiber/future/promise.hpp>

#include <cstdint>
#include <functional>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class BlockMetrics;
class BlockState;
class State;
struct BlockHeader;
struct CallTracerBase;
struct Chain;
struct Transaction;

using RevertTransactionFn = std::function<bool(
    Address const & /* sender */, Transaction const &, uint64_t /* i */,
    State &)>;

template <Traits traits>
Result<Receipt> dispatch_transaction(
    Chain const &chain, uint64_t const i, Transaction const &transaction,
    Address const &sender,
    std::vector<std::optional<Address>> const &authorities,
    BlockHeader const &header, BlockHashBuffer const &block_hash_buffer,
    BlockState &block_state, BlockMetrics &block_metrics,
    boost::fibers::promise<void> &prev, CallTracerBase &call_tracer,
    trace::StateTracer &state_tracer,
    RevertTransactionFn const &revert_transaction);

MONAD_NAMESPACE_END
