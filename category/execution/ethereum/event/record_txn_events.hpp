#pragma once

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/address.hpp>

#include <boost/fiber/future/promise.hpp>

#include <atomic>
#include <cstdint>
#include <optional>

enum monad_exec_account_access_context : uint8_t;

MONAD_NAMESPACE_BEGIN

struct ExecutionResult;
struct Transaction;

class State;

/// Record the TXN_START event, followed by the TXN_EVM_OUTPUT, TXN_REJECT, or
/// EVM_ERROR events, depending on what happened during transaction execution;
/// in the TXN_EVM_OUTPUT case, also record other execution output events
/// (TXN_LOG, TXN_CALL_FRAME, etc.)
void record_txn_events(
    uint32_t txn_num, Transaction const &, Address const &sender,
    Result<ExecutionResult> const &);

/// Record all account state accesses (both reads and writes) described by a
/// State object
void record_account_access_events(
    monad_exec_account_access_context, State const &);

MONAD_NAMESPACE_END
