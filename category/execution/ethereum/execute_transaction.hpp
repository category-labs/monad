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
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <span>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
struct BlockMetrics;
class BlockState;
struct CallTracerBase;
struct Chain;
template <Traits traits>
struct EvmcHost;
class State;
struct Transaction;

template <Traits traits>
class ExecuteTransactionNoValidation
{
    evmc_message to_message(
        vm::MemoryPool::Ref &msg_memory,
        std::uint32_t msg_memory_capacity) const;

    uint64_t process_authorizations(State &, EvmcHost<traits> &);

protected:
    Chain const &chain_;
    Transaction const &tx_;
    Address const &sender_;
    std::span<std::optional<Address> const> const authorities_;
    BlockHeader const &header_;

public:
    ExecuteTransactionNoValidation(
        Chain const &, Transaction const &, Address const &,
        std::span<std::optional<Address> const>, BlockHeader const &);

    evmc::Result operator()(State &, EvmcHost<traits> &);
};

template <Traits traits>
class ExecuteTransaction : public ExecuteTransactionNoValidation<traits>
{
    using ExecuteTransactionNoValidation<traits>::chain_;
    using ExecuteTransactionNoValidation<traits>::tx_;
    using ExecuteTransactionNoValidation<traits>::sender_;
    using ExecuteTransactionNoValidation<traits>::authorities_;
    using ExecuteTransactionNoValidation<traits>::header_;

    uint64_t i_;
    ChainContext<traits> const &chain_ctx_;
    BlockHashBuffer const &block_hash_buffer_;
    BlockState &block_state_;
    BlockMetrics &block_metrics_;
    boost::fibers::promise<void> &prev_;
    CallTracerBase &call_tracer_;
    trace::StateTracer &state_tracer_;

    Result<evmc::Result> execute_impl2(State &);
    Receipt execute_final(State &, evmc::Result const &);

public:
    ExecuteTransaction(
        Chain const &, uint64_t i, Transaction const &, Address const &,
        std::span<std::optional<Address> const>, BlockHeader const &,
        BlockHashBuffer const &, BlockState &, BlockMetrics &,
        boost::fibers::promise<void> &prev, CallTracerBase &,
        trace::StateTracer &, ChainContext<traits> const &chain_ctx);
    ~ExecuteTransaction() = default;

    Result<Receipt> operator()();
};

uint64_t g_star(
    evmc_revision, Transaction const &, uint64_t gas_remaining,
    uint64_t gas_refund);

MONAD_NAMESPACE_END
