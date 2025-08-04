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

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class BlockMetrics;
struct BlockHeader;
class BlockMetrics;
class BlockState;
struct CallTracerBase;
struct Chain;
template <evmc_revision rev>
struct EvmcHost;
class State;
struct Transaction;

template <evmc_revision rev>
class ExecuteTransactionNoValidation
{
    evmc_message to_message() const;

protected:
    Chain const &chain_;
    Transaction const &tx_;
    Address const &sender_;
    BlockHeader const &header_;

public:
    ExecuteTransactionNoValidation(
        Chain const &, Transaction const &, Address const &,
        BlockHeader const &);

    evmc::Result operator()(State &, EvmcHost<rev> &);
};

template <evmc_revision rev>
class ExecuteTransaction : public ExecuteTransactionNoValidation<rev>
{
    using ExecuteTransactionNoValidation<rev>::chain_;
    using ExecuteTransactionNoValidation<rev>::tx_;
    using ExecuteTransactionNoValidation<rev>::sender_;
    using ExecuteTransactionNoValidation<rev>::header_;

    uint64_t i_;
    BlockHashBuffer const &block_hash_buffer_;
    BlockState &block_state_;
    BlockMetrics &block_metrics_;
    boost::fibers::promise<void> &prev_;
    CallTracerBase &call_tracer_;
    std::unique_ptr<State> captured_state_;

    Result<evmc::Result> execute_impl2(State &);
    Receipt execute_final(State &, evmc::Result const &);

public:
    ExecuteTransaction(
        Chain const &, uint64_t i, Transaction const &, Address const &,
        BlockHeader const &, BlockHashBuffer const &, BlockState &,
        BlockMetrics &, boost::fibers::promise<void> &prev, CallTracerBase &);
    ~ExecuteTransaction() = default;

    Result<Receipt> operator()();

    std::unique_ptr<State> get_captured_state();
};

uint64_t g_star(
    evmc_revision, Transaction const &, uint64_t gas_remaining,
    uint64_t gas_refund);

MONAD_NAMESPACE_END
