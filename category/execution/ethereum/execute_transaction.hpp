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
#include <category/execution/ethereum/transaction_gas.hpp>
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

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
struct BlockHeader;
struct BlockMetrics;
class BlockState;
struct CallTracerBase;
struct Chain;
template <Traits traits>
struct EvmcHost;
class ExecutionEventRecorder;
class State;
struct Transaction;

template <Traits traits>
class ExecuteTransactionNoValidation
{
    evmc_message to_message(
        vm::MemoryPool::Ref &msg_memory, uint32_t msg_memory_capacity) const;

    uint64_t process_authorizations(State &, EvmcHost<traits> &);

protected:
    Chain const &chain_;
    Transaction const &tx_;
    Address const &sender_;
    std::span<std::optional<Address> const> const authorities_;
    BlockHeader const &header_;
    // Counted once here. Validation and execution each price the calldata
    // twice, and the counts are a pure function of tx_.data.
    CalldataTokens const tokens_;

public:
    ExecuteTransactionNoValidation(
        Chain const &, Transaction const &, Address const &,
        std::span<std::optional<Address> const>, BlockHeader const &);

    evmc::Result operator()(State &, EvmcHost<traits> &);
};

struct ZkvmSequentialExecutor;

// Permission to skip the merge-conflict check, which only a caller that has already serialized
// execution can hold.
//
// ExecuteTransaction's normal path runs a transaction BEFORE its predecessor has merged -- that
// is what `prev_` is for -- so the pre-state it read may be stale by the time it wants to merge.
// can_merge is what detects that, and the retry below it is what repairs it. A caller that runs
// one transaction at a time and merges each before constructing the next State has no CONCURRENT
// writer of block_state between this transaction's reads and its merge.
//
// The narrower statement, because the broader one is false: reads DO write block_state --
// BlockState::read_account, read_storage and read_code are non-const and emplace `{result,
// result}` on a cache miss. Both sides of every comparison can_merge makes come from that one
// emplace, so a non-concurrent mutation cannot make them disagree. can_merge therefore has
// nothing to detect: not "does not fail on our corpus", but no mechanism by which it could.
//
// That is a property of the SCHEDULER, not of the chain or the revision, so it is a token and not
// a trait -- ExecuteTransaction is explicitly instantiated for every traits set, and a second
// template parameter would multiply all of them for a property none of them describe.
//
// The constructor is private and befriended to one type. A caller cannot opt out of the check by
// writing a `true` at a call site; it has to be the type that owns a serialized loop.
class SequentialExecutionToken
{
    SequentialExecutionToken() = default;
    friend struct ZkvmSequentialExecutor;
};

template <Traits traits>
class ExecuteTransaction : public ExecuteTransactionNoValidation<traits>
{
    using ExecuteTransactionNoValidation<traits>::chain_;
    using ExecuteTransactionNoValidation<traits>::tx_;
    using ExecuteTransactionNoValidation<traits>::sender_;
    using ExecuteTransactionNoValidation<traits>::authorities_;
    using ExecuteTransactionNoValidation<traits>::header_;
    using ExecuteTransactionNoValidation<traits>::tokens_;

    uint64_t i_;
    ChainContext<traits> const &chain_ctx_;
    BlockHashBuffer const &block_hash_buffer_;
    BlockState &block_state_;
    BlockMetrics &block_metrics_;
    boost::fibers::promise<void> &prev_;
    CallTracerBase &call_tracer_;
    trace::StateTracer &state_tracer_;
    ExecutionEventRecorder *exec_recorder_;
    bool trace_transfers_;

    Result<evmc::Result> execute_impl2(State &);
    Receipt execute_final(State &, evmc::Result const &);

public:
    ExecuteTransaction(
        Chain const &, uint64_t i, Transaction const &, Address const &,
        std::span<std::optional<Address> const>, BlockHeader const &,
        BlockHashBuffer const &, BlockState &, BlockMetrics &,
        boost::fibers::promise<void> &prev, CallTracerBase &,
        trace::StateTracer &, ChainContext<traits> const &chain_ctx,
        ExecutionEventRecorder *exec_recorder, bool trace_transfers = false);
    ~ExecuteTransaction() = default;

    Result<Receipt> operator()();

    // For a caller holding SequentialExecutionToken. Waits on no predecessor and runs no
    // merge-conflict check, because neither can have anything to say; everything else --
    // execution, finalisation, the merge itself -- is the same work in the same order.
    //
    // MONAD_ZKVM_CHECK_SEQUENTIAL_MERGE restores the can_merge call as an assertion, so the
    // token's claim can be falsified by a build rather than trusted. It is forbidden in the
    // official profile, and absent from any build without it.
    Result<Receipt> execute(SequentialExecutionToken);
};

MONAD_NAMESPACE_END
