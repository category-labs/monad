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
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <evmc/evmc.h>

#include <memory>
#include <optional>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Block;
class BlockHashBuffer;
class BlockState;
struct Chain;

template <evmc_revision rev>
Result<std::vector<Receipt>> execute_block(
    Chain const &, Block &, std::vector<Address> const &senders, BlockState &,
    BlockHashBuffer const &, fiber::PriorityPool &, BlockMetrics &,
    std::vector<std::unique_ptr<CallTracerBase>> &);

Result<std::vector<Receipt>> execute_block(
    Chain const &, evmc_revision, Block &, std::vector<Address> const &senders,
    BlockState &, BlockHashBuffer const &, fiber::PriorityPool &,
    BlockMetrics &, std::vector<std::unique_ptr<CallTracerBase>> &);

std::vector<std::optional<Address>>
recover_senders(std::vector<Transaction> const &, fiber::PriorityPool &);

MONAD_NAMESPACE_END
