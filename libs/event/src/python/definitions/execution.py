from event_ctypes import *

#
# BLOCK_START
#

class block_exec_header(ctypes.Structure):
  _fields_ = (
    ('bft_block_id', bytes32),
    ('round', ctypes.c_uint64),
    ('parent_hash', bytes32),
    ('ommers_hash', bytes32),
    ('beneficiary', address),
    ('difficulty', ctypes.c_uint64),
    ('number', ctypes.c_uint64),
    ('gas_limit', ctypes.c_uint64),
    ('timestamp', ctypes.c_uint64),
    ('extra_data_length', ctypes.c_uint64),
    ('extra_data', bytes32),
    ('mix_hash', bytes32),
    ('nonce', ctypes.c_uint8 * 8),
    ('base_fee_per_gas', uint256_ne),
    ('txn_count', ctypes.c_uint64),
  )

register_event('BLOCK_START', block_exec_header,
    "Started execution of a proposed block")

#
# BLOCK_END
#

class block_exec_result(ctypes.Structure):
  _fields_ = (
    ('logs_bloom', ctypes.c_uint8 * 256),
    ('state_root', bytes32),
    ('transactions_root', bytes32),
    ('receipts_root', bytes32),
    ('withdrawals_root', bytes32),
    ('gas_used', ctypes.c_uint64)
  )

register_event('BLOCK_END', block_exec_result,
   "Proposed block with this flow ID has completed execution (may not be finalized)")

#
# BLOCK_FINALIZE
#

register_event('BLOCK_FINALIZE', None,
    "Block with this flow ID is commited as the canonical block on the chain")

#
# TXN_START
#

class txn_header(ctypes.Structure):
  _fields_ = (
    ('nonce', ctypes.c_uint64),
    ('gas_limit', ctypes.c_uint64),
    ('max_fee_per_gas', uint256_ne),
    ('value', uint256_ne),
    ('from', address),
    ('to', address),
    ('txn_type', transaction_type),
    ('r', uint256_ne),
    ('s', uint256_ne),
    ('y_parity', ctypes.c_uint8),
    ('chain_id', uint256_ne),
    ('data_length', ctypes.c_uint32),
  )

register_event('TXN_START', txn_header,
    "Started execution of new transaction")

#
# TXN_REJECT
#

# "long" payload value is the integral constant of the enum value of type
# `enum class TransactionError` from validate_transaction.hpp

register_event('TXN_REJECT', ctypes.c_long,
    "Transaction failed validation and was rejected - no receipt, not in block")

#
# TXN_EXEC_ERROR
#

class txn_exec_error(ctypes.Structure):
  _fields_ = (
    ('domain_id', ctypes.c_uint64),
    ('status_code', ctypes.c_long),
  )

register_event('TXN_EXEC_ERROR', txn_exec_error,
    "Transaction execution failed due to error in the EVM, not due to it being invalid")

#
# TXN_LOG
#

class txn_log(ctypes.Structure):
  _fields_ = (
    ('address', address),
    ('topic_count', ctypes.c_uint8),  # Size of bytes32 topic array after struct
    ('data_length', ctypes.c_uint32)  # Length of data placed after topic array
  )

register_event('TXN_LOG', txn_log,
    "Transaction emitted a log during speculative execution")

#
# TXN_RECEIPT
#

class txn_receipt(ctypes.Structure):
  _fields_ = (
    ('status', ctypes.c_uint64),
    ('gas_used', ctypes.c_uint64),
  )

register_event('TXN_RECEIPT', txn_receipt,
    "Transaction execution finished (merged into proposed block")

#
# WR_ACCT_STATE_BALANCE
#

class account_balance(ctypes.Structure):
  _fields_ = (
    ('address', address),
    ('balance', uint256_ne)
  )

register_event('WR_ACCT_STATE_BALANCE', account_balance,
    "Account balance updated by transaction commit")

#
# WR_ACCT_STATE_STORAGE
#

class account_storage(ctypes.Structure):
  _fields_ = (
    ('address', address),
    ('storage_key', bytes32),
    ('storage_value', bytes32)
  )

register_event('WR_ACCT_STATE_STORAGE', account_storage,
    "Account storage updated by transaction commit")
