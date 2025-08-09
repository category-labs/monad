#pragma once

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>

#include <boost/fiber/future/promise.hpp>
#include <evmc/evmc.hpp>

#include <cstdint>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class BlockMetrics;
struct BlockHeader;
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
    uint64_t i_;
    void *chain_context_;

public:
    ExecuteTransactionNoValidation(
        Chain const &, Transaction const &, Address const &,
        BlockHeader const &, uint64_t i, void *chain_context);

    evmc::Result operator()(State &, EvmcHost<rev> &, CallTracerBase &);
};

template <evmc_revision rev>
class ExecuteTransaction : public ExecuteTransactionNoValidation<rev>
{
    using ExecuteTransactionNoValidation<rev>::chain_;
    using ExecuteTransactionNoValidation<rev>::tx_;
    using ExecuteTransactionNoValidation<rev>::sender_;
    using ExecuteTransactionNoValidation<rev>::header_;
    using ExecuteTransactionNoValidation<rev>::i_;
    using ExecuteTransactionNoValidation<rev>::chain_context_;

    BlockHashBuffer const &block_hash_buffer_;
    BlockState &block_state_;
    BlockMetrics &block_metrics_;
    boost::fibers::promise<void> &prev_;
    CallTracerBase &call_tracer_;

    Result<evmc::Result> execute_impl2(State &);
    Receipt execute_final(State &, evmc::Result const &);

public:
    ExecuteTransaction(
        Chain const &, uint64_t i, Transaction const &, Address const &,
        BlockHeader const &, BlockHashBuffer const &, BlockState &,
        BlockMetrics &, boost::fibers::promise<void> &prev, CallTracerBase &,
        void *chain_context);
    ~ExecuteTransaction() = default;

    Result<Receipt> operator()();
};

uint64_t g_star(
    evmc_revision, Transaction const &, uint64_t gas_remaining,
    uint64_t gas_refund);

MONAD_NAMESPACE_END
