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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <span>
#include <string_view>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
struct BlockMetrics;
class BlockState;
struct CallTracerBase;
struct Chain;
template <Traits traits, bool gasless>
struct EvmcHost;
class State;
struct Transaction;

Receipt skipped_receipt(
    uint64_t transaction_index, uint64_t block_number,
    TransactionType transaction_type, std::string_view reason);

template <Traits traits, bool gasless = false>
class ExecuteTransactionNoValidation
{
    static_assert(!gasless || is_monad_trait_v<traits>);
    evmc_message to_message(
        vm::MemoryPool::Ref &msg_memory, uint32_t msg_memory_capacity) const;

    uint64_t process_authorizations(State &, EvmcHost<traits, gasless> &);

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

    evmc::Result operator()(State &, EvmcHost<traits, gasless> &);
};

template <Traits traits, bool gasless = false>
class ExecuteTransaction
    : public ExecuteTransactionNoValidation<traits, gasless>
{
    static_assert(!gasless || is_monad_trait_v<traits>);
    using ExecuteTransactionNoValidation<traits, gasless>::chain_;
    using ExecuteTransactionNoValidation<traits, gasless>::tx_;
    using ExecuteTransactionNoValidation<traits, gasless>::sender_;
    using ExecuteTransactionNoValidation<traits, gasless>::authorities_;
    using ExecuteTransactionNoValidation<traits, gasless>::header_;

    uint64_t i_;
    ChainContext<traits> const &chain_ctx_;
    BlockHashBuffer const &block_hash_buffer_;
    BlockState &block_state_;
    BlockMetrics &block_metrics_;
    boost::fibers::promise<void> &prev_;
    CallTracerBase &call_tracer_;
    trace::StateTracer &state_tracer_;
    bool trace_transfers_;
    std::optional<Address> domain_spoke_;

    Result<evmc::Result> execute_impl2(State &);
    Receipt execute_final(State &, evmc::Result const &);

public:
    ExecuteTransaction(
        Chain const &, uint64_t i, Transaction const &, Address const &,
        std::span<std::optional<Address> const>, BlockHeader const &,
        BlockHashBuffer const &, BlockState &, BlockMetrics &,
        boost::fibers::promise<void> &prev, CallTracerBase &,
        trace::StateTracer &, ChainContext<traits> const &chain_ctx,
        bool trace_transfers = false,
        std::optional<Address> domain_spoke = std::nullopt);
    ~ExecuteTransaction() = default;

    Result<Receipt> operator()();
};

MONAD_NAMESPACE_END
