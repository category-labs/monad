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

use std::{
    collections::HashMap,
    ffi::{CStr, CString},
    path::Path,
};

use alloy_consensus::{Header, Transaction as _, TxEnvelope};
use alloy_eips::eip2718::Encodable2718;
use alloy_primitives::{Address, Bytes, B256, U256, U64};
use alloy_rlp::Encodable;
use alloy_sol_types::decode_revert_reason;
use futures::channel::oneshot::{channel, Sender};
use serde::{Deserialize, Serialize};
use tracing::{error, info, warn};

use self::ffi::{monad_executor_result, PoolConfig};

pub mod ffi;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ChainId {
    EthereumMainnet,
    MonadMainnet,
    MonadTestnet,
    MonadDevnet,
    HiveNet,
}

impl ChainId {
    fn to_ffi_chain_config(self) -> ffi::monad_chain_config {
        match self {
            Self::EthereumMainnet => ffi::monad_chain_config_CHAIN_CONFIG_ETHEREUM_MAINNET,
            Self::MonadMainnet => ffi::monad_chain_config_CHAIN_CONFIG_MONAD_MAINNET,
            Self::MonadTestnet => ffi::monad_chain_config_CHAIN_CONFIG_MONAD_TESTNET,
            Self::MonadDevnet => ffi::monad_chain_config_CHAIN_CONFIG_MONAD_DEVNET,
            Self::HiveNet => ffi::monad_chain_config_CHAIN_CONFIG_HIVE_NET,
        }
    }
}

#[derive(Debug)]
pub struct EthCallExecutor {
    eth_call_executor: *mut ffi::monad_executor,
}

unsafe impl Send for EthCallExecutor {}
unsafe impl Sync for EthCallExecutor {}

impl EthCallExecutor {
    pub fn new(
        low_pool_config: PoolConfig,
        high_pool_config: PoolConfig,
        block_pool_config: PoolConfig,
        tx_exec_num_fibers: u32,
        node_lru_max_mem: u64,
        triedb_path: &Path,
    ) -> Self {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let dbpath = CString::new(triedb_path.to_str().expect("invalid path"))
            .expect("failed to create CString");

        let eth_call_executor = unsafe {
            ffi::monad_executor_create(
                low_pool_config,
                high_pool_config,
                block_pool_config,
                tx_exec_num_fibers,
                node_lru_max_mem,
                dbpath.as_c_str().as_ptr(),
            )
        };

        Self { eth_call_executor }
    }
}

impl Drop for EthCallExecutor {
    fn drop(&mut self) {
        info!("dropping eth_call_executor");
        unsafe {
            ffi::monad_executor_destroy(self.eth_call_executor);
        }
        info!("eth_call_executor successfully destroyed");
    }
}

// ensure that only one of {State, StateDiff} can be set
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum StorageOverride {
    State(HashMap<B256, B256>),
    StateDiff(HashMap<B256, B256>),
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct StateOverrideObject {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub balance: Option<U256>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub nonce: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code: Option<Bytes>,
    #[serde(flatten, default, skip_serializing_if = "Option::is_none")]
    pub storage_override: Option<StorageOverride>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum MonadTracer {
    NoopTracer = 0,
    CallTracer,
    PreStateTracer,
    StateDiffTracer,
    AccessListTracer,
}

impl From<MonadTracer> for u32 {
    fn from(tracer: MonadTracer) -> u32 {
        match tracer {
            MonadTracer::NoopTracer => 0,
            MonadTracer::CallTracer => 1,
            MonadTracer::PreStateTracer => 2,
            MonadTracer::StateDiffTracer => 3,
            MonadTracer::AccessListTracer => 4,
        }
    }
}

pub const ETH_CALL_SUCCESS: i32 = 0;
pub const EVMC_OUT_OF_GAS: i32 = 3;
pub const EVMC_MONAD_RESERVE_BALANCE_VIOLATION: i32 = 18;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum EthCallResult {
    Success,
    OutOfGas,
    ExecutionError,
    ReserveBalanceViolation,
    #[default]
    OtherError,
}

#[derive(Clone, Debug)]
pub enum CallResult {
    Success(SuccessCallResult),
    Failure(FailureCallResult),
    Revert(RevertCallResult), // only used for trace
}

#[derive(Clone, Debug, Default)]
pub struct SuccessCallResult {
    pub gas_used: u64,
    pub gas_refund: u64,
    // We interpret this as rlp encoded CallFrames for debug_traceCall
    pub output_data: Vec<u8>,
}

#[derive(Clone, Debug, Default)]
pub struct FailureCallResult {
    pub error_code: EthCallResult,
    pub gas_used: u64,
    pub gas_refund: u64,
    pub message: String,
    pub data: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct RevertCallResult {
    pub trace: Vec<u8>,
}

pub struct SenderContext {
    sender: Sender<*mut monad_executor_result>,
}

/// # Safety
/// This should be used only as a callback for monad_eth_call_executor_submit
///
/// This function is called when the eth_call is finished and the result is returned over the
/// channel
pub unsafe extern "C" fn eth_call_submit_callback(
    result: *mut monad_executor_result,
    user: *mut std::ffi::c_void,
) {
    let user = unsafe { Box::from_raw(user as *mut SenderContext) };

    let _ = user.sender.send(result);
}

pub type StateOverrideSet = HashMap<Address, StateOverrideObject>;

pub struct EthCallRequest<'a> {
    pub chain_id: ChainId,
    pub transaction: &'a TxEnvelope,
    pub block_header: &'a Header,
    pub sender: Address,
    pub block_number: u64,
    pub block_id: Option<[u8; 32]>,
    pub state_override_set: &'a StateOverrideSet,
    pub tracer: MonadTracer,
    pub gas_specified: bool,
}

pub async fn eth_call(
    request: EthCallRequest<'_>,
    eth_call_executor: &EthCallExecutor,
) -> CallResult {
    let EthCallRequest {
        chain_id,
        transaction,
        block_header,
        sender,
        block_number,
        block_id,
        state_override_set,
        tracer,
        gas_specified,
    } = request;

    if transaction.gas_limit() > block_header.gas_limit {
        return CallResult::Failure(FailureCallResult {
            error_code: EthCallResult::OtherError,
            message: "gas limit too high".into(),
            data: None,
            ..Default::default()
        });
    }

    let mut rlp_encoded_tx = vec![];
    transaction.encode_2718(&mut rlp_encoded_tx);

    let mut rlp_encoded_block_header = vec![];
    block_header.encode(&mut rlp_encoded_block_header);

    let mut rlp_encoded_sender = vec![];
    sender.encode(&mut rlp_encoded_sender);

    let override_ctx = unsafe { ffi::monad_state_override_create() };
    for (addr, obj) in state_override_set {
        let addr: &[u8] = addr.as_slice();

        unsafe {
            ffi::add_override_address(override_ctx, addr.as_ptr(), addr.len());

            if let Some(balance) = obj.balance {
                // Big Endianness is to match with decode in eth_call.cpp (intx::be::load)
                let balance_vec = balance.to_be_bytes_vec();

                ffi::set_override_balance(
                    override_ctx,
                    addr.as_ptr(),
                    addr.len(),
                    balance_vec.as_ptr(),
                    balance_vec.len(),
                );
            }

            if let Some(nonce) = obj.nonce {
                ffi::set_override_nonce(
                    override_ctx,
                    addr.as_ptr(),
                    addr.len(),
                    nonce.as_limbs()[0],
                )
            }

            if let Some(code) = &obj.code {
                ffi::set_override_code(
                    override_ctx,
                    addr.as_ptr(),
                    addr.len(),
                    code.as_ptr(),
                    code.len(),
                )
            }

            match &obj.storage_override {
                Some(StorageOverride::State(storage_override)) => {
                    for (k, v) in storage_override {
                        ffi::set_override_state(
                            override_ctx,
                            addr.as_ptr(),
                            addr.len(),
                            k.as_ptr(),
                            k.len(),
                            v.as_ptr(),
                            v.len(),
                        )
                    }
                }
                Some(StorageOverride::StateDiff(override_state_diff)) => {
                    for (k, v) in override_state_diff {
                        ffi::set_override_state_diff(
                            override_ctx,
                            addr.as_ptr(),
                            addr.len(),
                            k.as_ptr(),
                            k.len(),
                            v.as_ptr(),
                            v.len(),
                        )
                    }
                }
                None => {}
            }
        }
    }

    let chain_config = chain_id.to_ffi_chain_config();

    let block_id = block_id.unwrap_or([0_u8; 32]);
    let rlp_encoded_block_id = alloy_rlp::encode(block_id);

    let (send, recv) = channel();
    let sender_ctx = Box::new(SenderContext { sender: send });

    unsafe {
        let sender_ctx_ptr = Box::into_raw(sender_ctx);

        ffi::monad_executor_eth_call_submit(
            eth_call_executor.eth_call_executor,
            chain_config,
            rlp_encoded_tx.as_ptr(),
            rlp_encoded_tx.len(),
            rlp_encoded_block_header.as_ptr(),
            rlp_encoded_block_header.len(),
            rlp_encoded_sender.as_ptr(),
            rlp_encoded_sender.len(),
            block_number,
            rlp_encoded_block_id.as_ptr(),
            rlp_encoded_block_id.len(),
            override_ctx,
            Some(eth_call_submit_callback),
            sender_ctx_ptr as *mut std::ffi::c_void,
            tracer.into(),
            gas_specified,
        )
    };

    let result = match recv.await {
        Ok(r) => r,
        Err(e) => {
            unsafe { ffi::monad_state_override_destroy(override_ctx) };

            warn!("callback from eth_call_executor failed: {:?}", e);

            return CallResult::Failure(FailureCallResult {
                error_code: EthCallResult::OtherError,
                message: "internal eth_call error".to_string(),
                data: None,
                ..Default::default()
            });
        }
    };

    unsafe {
        let status_code = (*result).status_code;
        let tracer_cval: u32 = tracer.into();

        let call_result = match status_code {
            ETH_CALL_SUCCESS => {
                let gas_used = (*result).gas_used as u64;
                let gas_refund = (*result).gas_refund as u64;

                if tracer_cval == ffi::monad_tracer_config_NOOP_TRACER {
                    let output_data_len = (*result).output_data_len;
                    let output_data = if output_data_len != 0 {
                        std::slice::from_raw_parts((*result).output_data, output_data_len).to_vec()
                    } else {
                        vec![]
                    };

                    CallResult::Success(SuccessCallResult {
                        gas_used,
                        gas_refund,
                        output_data,
                    })
                } else {
                    let output_data_len = (*result).encoded_trace_len;
                    let output_data = if output_data_len != 0 {
                        std::slice::from_raw_parts((*result).encoded_trace, output_data_len)
                            .to_vec()
                    } else {
                        vec![]
                    };

                    CallResult::Success(SuccessCallResult {
                        gas_used,
                        gas_refund,
                        output_data,
                    })
                }
            }
            EVMC_MONAD_RESERVE_BALANCE_VIOLATION => {
                if tracer_cval == ffi::monad_tracer_config_NOOP_TRACER {
                    CallResult::Failure(FailureCallResult {
                        error_code: EthCallResult::ReserveBalanceViolation,
                        gas_used: (*result).gas_used as u64,
                        gas_refund: (*result).gas_refund as u64,
                        message: "reserve balance violation".to_string(),
                        data: None,
                    })
                } else {
                    let output_data_len = (*result).encoded_trace_len;
                    let output_data = if output_data_len != 0 {
                        std::slice::from_raw_parts((*result).encoded_trace, output_data_len)
                            .to_vec()
                    } else {
                        vec![]
                    };
                    CallResult::Revert(RevertCallResult { trace: output_data })
                }
            }
            _ => {
                if (*result).message.is_null() {
                    // This means execution reverted, not a validation error
                    if tracer_cval == ffi::monad_tracer_config_NOOP_TRACER {
                        let output_data_len = (*result).output_data_len;
                        let output_data = if output_data_len != 0 {
                            std::slice::from_raw_parts((*result).output_data, output_data_len)
                                .to_vec()
                        } else {
                            vec![]
                        };

                        let message = String::from("execution reverted");
                        let formatted_message = match decode_revert_message(&output_data) {
                            Some(error_message) => format!("{}: {}", message, error_message),
                            None => message,
                        };

                        CallResult::Failure(FailureCallResult {
                            error_code: if status_code == EVMC_OUT_OF_GAS {
                                EthCallResult::OutOfGas
                            } else {
                                EthCallResult::ExecutionError
                            },
                            gas_used: (*result).gas_used as u64,
                            gas_refund: (*result).gas_refund as u64,
                            message: formatted_message,
                            data: Some(format!("0x{}", hex::encode(&output_data))),
                        })
                    } else {
                        let output_data_len = (*result).encoded_trace_len;
                        let output_data = if output_data_len != 0 {
                            std::slice::from_raw_parts((*result).encoded_trace, output_data_len)
                                .to_vec()
                        } else {
                            vec![]
                        };
                        CallResult::Revert(RevertCallResult { trace: output_data })
                    }
                } else {
                    // This means we hit a validation error (execution not started)
                    let cstr_msg = CStr::from_ptr((*result).message.cast());
                    let message = match cstr_msg.to_str() {
                        Ok(str) => String::from(str),
                        Err(_) => String::from("execution error eth_call message invalid utf-8"),
                    };

                    CallResult::Failure(FailureCallResult {
                        error_code: EthCallResult::OtherError,
                        message,
                        data: None,
                        ..Default::default()
                    })
                }
            }
        };

        ffi::monad_executor_result_release(result);
        ffi::monad_state_override_destroy(override_ctx);

        call_result
    }
}

pub fn decode_revert_message(output_data: &[u8]) -> Option<String> {
    // https://docs.soliditylang.org/en/latest/control-structures.html#revert
    decode_revert_reason(output_data).and_then(|message| {
        let parsed_message = message
            .strip_prefix("revert: ")
            .or_else(|| message.strip_prefix("panic: "))
            .unwrap_or(&message)
            .trim();
        if parsed_message.is_empty() {
            None
        } else {
            Some(parsed_message.to_string())
        }
    })
}

pub async fn eth_trace_block_or_transaction(
    chain_id: ChainId,
    block_header: Header,
    block_number: u64,
    block_id: Option<[u8; 32]>,
    parent_id: Option<[u8; 32]>,
    grandparent_id: Option<[u8; 32]>,
    transaction_index: i64,
    eth_call_executor: &EthCallExecutor,
    tracer: MonadTracer,
) -> CallResult {
    let chain_config = chain_id.to_ffi_chain_config();

    let mut rlp_encoded_block_header = vec![];
    block_header.encode(&mut rlp_encoded_block_header);

    let rlp_encoded_block_id = alloy_rlp::encode(block_id.unwrap_or([0_u8; 32]));

    let rlp_encoded_parent_id = alloy_rlp::encode(parent_id.unwrap_or([0_u8; 32]));

    let rlp_encoded_grandparent_id = alloy_rlp::encode(grandparent_id.unwrap_or([0_u8; 32]));

    let (send, recv) = channel();
    let sender_ctx = Box::new(SenderContext { sender: send });

    unsafe {
        let sender_ctx_ptr = Box::into_raw(sender_ctx);

        ffi::monad_executor_run_transactions(
            eth_call_executor.eth_call_executor,
            chain_config,
            rlp_encoded_block_header.as_ptr(),
            rlp_encoded_block_header.len(),
            block_number,
            rlp_encoded_block_id.as_ptr(),
            rlp_encoded_block_id.len(),
            rlp_encoded_parent_id.as_ptr(),
            rlp_encoded_parent_id.len(),
            rlp_encoded_grandparent_id.as_ptr(),
            rlp_encoded_grandparent_id.len(),
            transaction_index,
            Some(eth_call_submit_callback),
            sender_ctx_ptr as *mut std::ffi::c_void,
            tracer.into(),
        )
    };

    let result = match recv.await {
        Ok(r) => r,
        Err(e) => {
            warn!(
                "callback from eth_trace_block_or_transaction_executor failed: {:?}",
                e
            );

            return CallResult::Failure(FailureCallResult {
                error_code: EthCallResult::OtherError,
                message: "internal eth_trace_block_or_transaction error".to_string(),
                data: None,
                ..Default::default()
            });
        }
    };

    unsafe {
        let status_code = (*result).status_code;

        let call_result = match status_code {
            ETH_CALL_SUCCESS => {
                // TODO(dhil): I don't think these matter for the output of prestate tracing. Other providers don't seem to return them in prestate mode.
                let gas_used = (*result).gas_used as u64;
                let gas_refund = (*result).gas_refund as u64;

                let output_data_len = (*result).encoded_trace_len;
                let output_data = if output_data_len != 0 {
                    std::slice::from_raw_parts((*result).encoded_trace, output_data_len).to_vec()
                } else {
                    vec![]
                };

                CallResult::Success(SuccessCallResult {
                    gas_used,
                    gas_refund,
                    output_data,
                })
            }
            _ => {
                let cstr_msg = (!(*result).message.is_null())
                    .then(|| CStr::from_ptr((*result).message.cast()));

                let message = match cstr_msg.map(CStr::to_str) {
                    Some(Ok(str)) => String::from(str),
                    Some(Err(_)) => String::from(
                        "execution error eth_trace_block_or_transaction message invalid utf-8",
                    ),
                    None => {
                        error!("callback from eth_trace_block_or_transaction_executor failed: message pointer is null");
                        String::from("callback from eth_trace_block_or_transaction_executor failed: message pointer is null")
                    }
                };

                CallResult::Failure(FailureCallResult {
                    error_code: EthCallResult::OtherError,
                    message,
                    data: None,
                    ..Default::default()
                })
            }
        };

        ffi::monad_executor_result_release(result);

        call_result
    }
}

#[cfg(test)]
mod tests {
    use alloy_primitives::hex;

    use super::*;

    #[test]
    fn test_decode_revert_message() {
        // https://github.com/ethereum/execution-apis/blob/37c2b9e/tests/eth_call/call-revert-abi-error.io
        let data = hex::decode(
            "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a75736572206572726f72"
        ).unwrap();
        let message = decode_revert_message(&data).unwrap();
        assert_eq!(message, String::from("user error"));

        // https://github.com/ethereum/execution-apis/blob/37c2b9e/tests/eth_call/call-revert-abi-panic.io
        let data = hex::decode(
            "0x4e487b710000000000000000000000000000000000000000000000000000000000000001",
        )
        .unwrap();
        let message = decode_revert_message(&data).unwrap();
        assert_eq!(message, String::from("assertion failed (0x01)"));
    }
}
