#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/result.hpp>

#include <boost/fiber/future/promise.hpp>

#include <atomic>
#include <cstdint>
#include <optional>

enum monad_exec_account_access_context : uint8_t;

MONAD_NAMESPACE_BEGIN

struct ExecutionResult;
struct Transaction;

class State;

/// Record the TXN_START event
void record_txn_start_event(
    uint32_t txn_num, Transaction const &, Address const &sender,
    uint64_t ingest_epoch_nanos, boost::fibers::promise<void> &txn_record_sync);

/// Record the TXN_EVM_OUTPUT, TXN_REJECT, or EVM_ERROR events, depending on
/// what happened during transaction execution; in the TXN_EVM_OUTPUT case,
/// this also records many other events (logs, call frames, etc.)
void record_txn_exec_result_events(
    uint32_t txn_num, Result<ExecutionResult> const &);

/// Record all account state accesses (both reads and writes) described by a
/// State object
void record_account_access_events(
    monad_exec_account_access_context, State const &);

MONAD_NAMESPACE_END
