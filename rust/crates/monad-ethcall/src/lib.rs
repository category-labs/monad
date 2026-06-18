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
    ptr::NonNull,
};

use alloy_consensus::{Header, Transaction as _, TxEnvelope};
use alloy_eips::{eip2718::Encodable2718, eip4895::Withdrawal};
use alloy_primitives::{Address, Bytes, FixedBytes, B256, U256, U64};
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
    ) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let path_str = triedb_path.to_str()?;

        let dbpath = CString::new(path_str).ok()?;

        let mut eth_call_executor: *mut ffi::monad_executor = std::ptr::null_mut();
        let status = unsafe {
            ffi::monad_executor_create(
                low_pool_config,
                high_pool_config,
                block_pool_config,
                tx_exec_num_fibers,
                node_lru_max_mem,
                dbpath.as_c_str().as_ptr(),
                &mut eth_call_executor,
            )
        };

        if status != ffi::MONAD_EXECUTOR_OK || eth_call_executor.is_null() {
            return None;
        }

        Some(Self { eth_call_executor })
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

struct MonadExecutorResult {
    c_handle: NonNull<ffi::monad_executor_result>,
}

impl MonadExecutorResult {
    fn from_c_handle(c_handle: *mut ffi::monad_executor_result) -> Option<Self> {
        NonNull::new(c_handle).map(|h| Self { c_handle: h })
    }

    fn status_code(&self) -> i32 {
        unsafe { (*self.c_handle.as_ptr()).status_code }
    }

    fn encoded_trace(&self) -> Result<Box<[u8]>, ()> {
        let this = unsafe { *self.c_handle.as_ref() };

        if this.encoded_trace_len == 0 {
            return Ok(Box::new([]));
        }

        if this.encoded_trace.is_null() {
            return Err(());
        }

        Ok(Box::from(unsafe {
            std::slice::from_raw_parts(this.encoded_trace, this.encoded_trace_len)
        }))
    }

    fn message(&self) -> String {
        let cstr_msg = unsafe { CStr::from_ptr((*self.c_handle.as_ptr()).message.cast()) };
        String::from(
            cstr_msg
                .to_str()
                .unwrap_or("execution error: message invalid utf-8"),
        )
    }
}

impl Drop for MonadExecutorResult {
    fn drop(&mut self) {
        unsafe {
            ffi::monad_executor_result_release(self.c_handle.as_ptr());
        }
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

fn override_status_message(status: ffi::monad_override_status_code_t) -> &'static str {
    match status {
        ffi::monad_override_status_code_t::MONAD_OVERRIDE_OK => "ok",
        ffi::monad_override_status_code_t::MONAD_OVERRIDE_EINVAL => "invalid argument",
        ffi::monad_override_status_code_t::MONAD_OVERRIDE_ENOMEM => "out of memory",
        ffi::monad_override_status_code_t::MONAD_OVERRIDE_EEXIST => "entry already exists",
        ffi::monad_override_status_code_t::MONAD_OVERRIDE_ENOENT => "entry not found",
        ffi::monad_override_status_code_t::MONAD_OVERRIDE_EUNKNOWN => "unknown error",
    }
}

fn executor_status_message(status: ffi::monad_executor_status_code_t) -> &'static str {
    match status {
        ffi::monad_executor_status_code_t::MONAD_EXECUTOR_OK => "ok",
        ffi::monad_executor_status_code_t::MONAD_EXECUTOR_EINVAL => "invalid argument",
        ffi::monad_executor_status_code_t::MONAD_EXECUTOR_ENOMEM => "out of memory",
        ffi::monad_executor_status_code_t::MONAD_EXECUTOR_ERLP_DECODE => "RLP decode failed",
        ffi::monad_executor_status_code_t::MONAD_EXECUTOR_ERLP_TRAILING => "RLP trailing bytes",
        ffi::monad_executor_status_code_t::MONAD_EXECUTOR_ESIZE_MISMATCH => "size mismatch",
        ffi::monad_executor_status_code_t::MONAD_EXECUTOR_EUNKNOWN => "unknown error",
    }
}

fn ensure_override_ok(status: ffi::monad_override_status_code_t) -> Result<(), &'static str> {
    if status == ffi::monad_override_status_code_t::MONAD_OVERRIDE_OK {
        return Ok(());
    }

    Err(override_status_message(status))
}

fn ensure_executor_ok(status: ffi::monad_executor_status_code_t) -> Result<(), &'static str> {
    if status == ffi::monad_executor_status_code_t::MONAD_EXECUTOR_OK {
        return Ok(());
    }

    Err(executor_status_message(status))
}

fn call_failure_with_message(message: impl Into<String>) -> CallResult {
    // TODO(dhil): It would be desirable to have non-allocating error-variant here to ensure the RPC process is resilient to OOM errors.
    CallResult::Failure(FailureCallResult {
        error_code: EthCallResult::OtherError,
        message: message.into(),
        data: None,
        ..Default::default()
    })
}

fn simulate_failure_with_message(message: impl Into<String>) -> SimulateResult {
    SimulateResult::Failure(FailureSimulateResult {
        error_code: EthCallResult::OtherError,
        message: message.into(),
        data: None,
    })
}

macro_rules! return_call_failure_on_err {
    ($expr:expr) => {
        if let Err(message) = $expr {
            warn!("{}", message);
            return call_failure_with_message(message);
        }
    };
    ($expr:expr, $cleanup:expr) => {
        if let Err(message) = $expr {
            warn!("{}", message);
            $cleanup;
            return call_failure_with_message(message);
        }
    };
}

macro_rules! return_simulate_failure_on_err {
    ($expr:expr) => {
        if let Err(message) = $expr {
            warn!("{}", message);
            return simulate_failure_with_message(message);
        }
    };
    ($expr:expr, $cleanup:expr) => {
        if let Err(message) = $expr {
            warn!("{}", message);
            $cleanup;
            return simulate_failure_with_message(message);
        }
    };
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

struct CStateOverride {
    c_handle: NonNull<ffi::monad_state_override>,
}

impl CStateOverride {
    fn new() -> Option<Self> {
        let mut c_handle: *mut ffi::monad_state_override = std::ptr::null_mut();
        let status = unsafe { ffi::monad_state_override_create(&mut c_handle) };
        if status != ffi::monad_override_status_code_t::MONAD_OVERRIDE_OK {
            return None;
        }
        NonNull::new(c_handle).map(|c_handle| Self { c_handle })
    }

    fn as_mut_ptr(&mut self) -> *mut ffi::monad_state_override {
        self.c_handle.as_ptr()
    }
}

impl Drop for CStateOverride {
    fn drop(&mut self) {
        unsafe {
            ffi::monad_state_override_destroy(self.c_handle.as_ptr());
        }
    }
}

#[derive(Clone, Debug)]
pub enum SimulateResult {
    Success(SuccessSimulateResult),
    Failure(FailureSimulateResult),
}

#[derive(Clone, Debug)]
pub struct SuccessSimulateResult {
    pub output_data: Box<[u8]>,
}

#[derive(Clone, Debug)]
pub struct FailureSimulateResult {
    pub error_code: EthCallResult,
    pub message: String,
    pub data: Option<String>,
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

    let Some(mut override_ctx) = CStateOverride::new() else {
        warn!("failed to create state override");

        return call_failure_with_message(
            "internal eth_call error: failed to create state override".to_string(),
        );
    };
    let override_ctx_ptr = override_ctx.as_mut_ptr();

    for (addr, obj) in state_override_set {
        let addr: &[u8] = addr.as_slice();

        unsafe {
            let status = ffi::add_override_address(override_ctx_ptr, addr.as_ptr(), addr.len());
            return_call_failure_on_err!(ensure_override_ok(status));

            if let Some(balance) = obj.balance {
                // Big Endianness is to match with decode in eth_call.cpp (intx::be::load)
                let balance_vec = balance.to_be_bytes_vec();

                let status = ffi::set_override_balance(
                    override_ctx_ptr,
                    addr.as_ptr(),
                    addr.len(),
                    balance_vec.as_ptr(),
                    balance_vec.len(),
                );
                return_call_failure_on_err!(ensure_override_ok(status));
            }

            if let Some(nonce) = obj.nonce {
                let status = ffi::set_override_nonce(
                    override_ctx_ptr,
                    addr.as_ptr(),
                    addr.len(),
                    nonce.as_limbs()[0],
                );
                return_call_failure_on_err!(ensure_override_ok(status));
            }

            if let Some(code) = &obj.code {
                let status = ffi::set_override_code(
                    override_ctx_ptr,
                    addr.as_ptr(),
                    addr.len(),
                    code.as_ptr(),
                    code.len(),
                );
                return_call_failure_on_err!(ensure_override_ok(status));
            }

            match &obj.storage_override {
                Some(StorageOverride::State(storage_override)) => {
                    for (k, v) in storage_override {
                        let status = ffi::set_override_state(
                            override_ctx_ptr,
                            addr.as_ptr(),
                            addr.len(),
                            k.as_ptr(),
                            k.len(),
                            v.as_ptr(),
                            v.len(),
                        );
                        return_call_failure_on_err!(ensure_override_ok(status));
                    }
                }
                Some(StorageOverride::StateDiff(override_state_diff)) => {
                    for (k, v) in override_state_diff {
                        let status = ffi::set_override_state_diff(
                            override_ctx_ptr,
                            addr.as_ptr(),
                            addr.len(),
                            k.as_ptr(),
                            k.len(),
                            v.as_ptr(),
                            v.len(),
                        );
                        return_call_failure_on_err!(ensure_override_ok(status));
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

        let status = ffi::monad_executor_eth_call_submit(
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
            override_ctx_ptr,
            Some(eth_call_submit_callback),
            sender_ctx_ptr as *mut std::ffi::c_void,
            tracer.into(),
            gas_specified,
        );
        return_call_failure_on_err!(ensure_executor_ok(status), {
            let _ = Box::from_raw(sender_ctx_ptr); // reclaims ownership in the event of an error status code.
        });
    };

    let result = match recv.await {
        Ok(r) => r,
        Err(e) => {
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

        let status = ffi::monad_executor_run_transactions(
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
        );
        return_call_failure_on_err!(ensure_executor_ok(status), {
            let _ = Box::from_raw(sender_ctx_ptr); // reclaims ownership in the event of an error status code.
        });
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

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct BlockOverride {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub number: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub gas_limit: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fee_recipient: Option<Address>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prev_randao: Option<B256>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base_fee_per_gas: Option<U256>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub withdrawals: Vec<Withdrawal>,
}

struct CStateOverrideVec {
    c_handle: NonNull<ffi::monad_state_override_vec>,
}

impl CStateOverrideVec {
    fn with_capacity(size: usize) -> Option<Self> {
        let mut c_handle: *mut ffi::monad_state_override_vec = std::ptr::null_mut();
        let status = unsafe { ffi::monad_state_override_vec_create(size, &mut c_handle) };
        if status != ffi::monad_override_status_code_t::MONAD_OVERRIDE_OK {
            return None;
        }
        NonNull::new(c_handle).map(|c_handle| Self { c_handle })
    }

    fn as_mut_ptr(&mut self) -> *mut ffi::monad_state_override_vec {
        self.c_handle.as_ptr()
    }

    fn add_address_at(&mut self, at: usize, addr: &Address) -> Result<(), &'static str> {
        let addr: &[u8] = addr.as_slice();
        let status = unsafe {
            ffi::add_override_address_at(self.as_mut_ptr(), at, addr.as_ptr(), addr.len())
        };
        ensure_override_ok(status)
    }

    fn set_balance_at(
        &mut self,
        at: usize,
        addr: &Address,
        balance: &U256,
    ) -> Result<(), &'static str> {
        // Big Endianess is to match with decode in eth_call.cpp (intx::be::load)
        let balance_bytes = balance.to_be_bytes_vec();
        let addr: &[u8] = addr.as_slice();
        let status = unsafe {
            ffi::set_override_balance_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                balance_bytes.as_ptr(),
                balance_bytes.len(),
            )
        };
        ensure_override_ok(status)
    }

    fn set_nonce_at(&mut self, at: usize, addr: &Address, nonce: u64) -> Result<(), &'static str> {
        let addr: &[u8] = addr.as_slice();
        let status = unsafe {
            ffi::set_override_nonce_at(self.as_mut_ptr(), at, addr.as_ptr(), addr.len(), nonce)
        };
        ensure_override_ok(status)
    }

    fn set_code_at(&mut self, at: usize, addr: &Address, code: &Bytes) -> Result<(), &'static str> {
        let addr: &[u8] = addr.as_slice();
        let status = unsafe {
            ffi::set_override_code_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                code.as_ptr(),
                code.len(),
            )
        };
        ensure_override_ok(status)
    }

    fn set_state_at(
        &mut self,
        at: usize,
        addr: &Address,
        key: &FixedBytes<32>,
        value: &FixedBytes<32>,
    ) -> Result<(), &'static str> {
        let addr: &[u8] = addr.as_slice();
        let status = unsafe {
            ffi::set_override_state_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                key.as_ptr(),
                key.len(),
                value.as_ptr(),
                value.len(),
            )
        };
        ensure_override_ok(status)
    }

    fn set_state_diff_at(
        &mut self,
        at: usize,
        addr: &Address,
        key: &FixedBytes<32>,
        value: &FixedBytes<32>,
    ) -> Result<(), &'static str> {
        let addr: &[u8] = addr.as_slice();
        let status = unsafe {
            ffi::set_override_state_diff_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                key.as_ptr(),
                key.len(),
                value.as_ptr(),
                value.len(),
            )
        };
        ensure_override_ok(status)
    }
}

impl Drop for CStateOverrideVec {
    fn drop(&mut self) {
        unsafe {
            ffi::monad_state_override_vec_destroy(self.c_handle.as_ptr());
        }
    }
}
struct CBlockOverrideVec {
    c_handle: NonNull<ffi::monad_block_override_vec>,
}

impl CBlockOverrideVec {
    fn with_capacity(size: usize) -> Option<Self> {
        let mut c_handle: *mut ffi::monad_block_override_vec = std::ptr::null_mut();
        let status = unsafe { ffi::monad_block_override_vec_create(size, &mut c_handle) };
        if status != ffi::monad_override_status_code_t::MONAD_OVERRIDE_OK {
            return None;
        }
        NonNull::new(c_handle).map(|c_handle| Self { c_handle })
    }

    fn as_mut_ptr(&mut self) -> *mut ffi::monad_block_override_vec {
        self.c_handle.as_ptr()
    }

    fn set_number_at(&mut self, i: usize, number: u64) -> Result<(), &'static str> {
        let status = unsafe { ffi::set_block_override_number_at(self.as_mut_ptr(), i, number) };
        ensure_override_ok(status)
    }

    fn set_time_at(&mut self, i: usize, time: u64) -> Result<(), &'static str> {
        let status = unsafe { ffi::set_block_override_time_at(self.as_mut_ptr(), i, time) };
        ensure_override_ok(status)
    }

    fn set_gas_limit_at(&mut self, i: usize, gas_limit: u64) -> Result<(), &'static str> {
        let status =
            unsafe { ffi::set_block_override_gas_limit_at(self.as_mut_ptr(), i, gas_limit) };
        ensure_override_ok(status)
    }

    fn set_fee_recipient_at(
        &mut self,
        i: usize,
        fee_recipient: &Address,
    ) -> Result<(), &'static str> {
        let fee_recipient_bytes: &[u8] = fee_recipient.as_slice();
        let status = unsafe {
            ffi::set_block_override_fee_recipient_at(
                self.as_mut_ptr(),
                i,
                fee_recipient_bytes.as_ptr(),
                fee_recipient_bytes.len(),
            )
        };
        ensure_override_ok(status)
    }

    fn set_prev_randao_at(
        &mut self,
        i: usize,
        prev_randao: &FixedBytes<32>,
    ) -> Result<(), &'static str> {
        let prev_randao_bytes: &[u8] = prev_randao.as_slice();
        let status = unsafe {
            ffi::set_block_override_prev_randao_at(
                self.as_mut_ptr(),
                i,
                prev_randao_bytes.as_ptr(),
                prev_randao_bytes.len(),
            )
        };
        ensure_override_ok(status)
    }

    fn set_base_fee_per_gas_at(
        &mut self,
        i: usize,
        base_fee_per_gas: &U256,
    ) -> Result<(), &'static str> {
        let base_fee_per_gas_vec = base_fee_per_gas.to_be_bytes_vec();
        let status = unsafe {
            ffi::set_block_override_base_fee_per_gas_at(
                self.as_mut_ptr(),
                i,
                base_fee_per_gas_vec.as_ptr(),
                base_fee_per_gas_vec.len(),
            )
        };
        ensure_override_ok(status)
    }

    fn add_withdrawal_at(&mut self, i: usize, withdrawal: &Withdrawal) -> Result<(), &'static str> {
        let address_bytes: &[u8] = withdrawal.address.as_slice();
        let status = unsafe {
            ffi::add_block_override_withdrawal_at(
                self.as_mut_ptr(),
                i,
                withdrawal.index,
                withdrawal.validator_index,
                withdrawal.amount,
                address_bytes.as_ptr(),
                address_bytes.len(),
            )
        };
        ensure_override_ok(status)
    }
}

impl Drop for CBlockOverrideVec {
    fn drop(&mut self) {
        unsafe {
            ffi::monad_block_override_vec_destroy(self.c_handle.as_ptr());
        }
    }
}

pub async fn eth_simulate_v1(
    chain_id: ChainId,
    senders: &Vec<Vec<Address>>,
    calls: &Vec<Vec<TxEnvelope>>,
    block_header: Header,
    block_number: u64,
    block_id: Option<[u8; 32]>,
    grandparent_id: Option<[u8; 32]>,
    gas_limit: u64,
    max_calls: usize,
    emit_native_transfer_logs: bool,
    eth_call_executor: &EthCallExecutor,
    overrides: &[(&BlockOverride, &StateOverrideSet)],
) -> SimulateResult {
    assert_eq!(calls.len(), overrides.len());
    assert_eq!(calls.len(), senders.len());

    for (txs, senders) in calls.iter().zip(senders.iter()) {
        assert_eq!(txs.len(), senders.len());
    }

    let mut rlp_encoded_senders = vec![];
    senders.encode(&mut rlp_encoded_senders);

    let mut rlp_encoded_txns = vec![];
    calls.encode(&mut rlp_encoded_txns);

    let mut rlp_encoded_block_header = vec![];
    block_header.encode(&mut rlp_encoded_block_header);

    let rlp_encoded_block_id = alloy_rlp::encode(block_id.unwrap_or([0_u8; 32]));
    let rlp_encoded_grandparent_id = alloy_rlp::encode(grandparent_id.unwrap_or([0_u8; 32]));

    let chain_config = chain_id.to_ffi_chain_config();

    let Some(mut state_overrides) = CStateOverrideVec::with_capacity(calls.len()) else {
        warn!("failed to create state override vector");

        return SimulateResult::Failure(FailureSimulateResult {
            error_code: EthCallResult::OtherError,
            message: "internal eth_simulate_v1 error: failed to create state override vector"
                .to_string(),
            data: None,
        });
    };
    let Some(mut block_overrides) = CBlockOverrideVec::with_capacity(calls.len()) else {
        warn!("failed to create block override vector");

        return SimulateResult::Failure(FailureSimulateResult {
            error_code: EthCallResult::OtherError,
            message: "internal eth_simulate_v1 error: failed to create block override vector"
                .to_string(),
            data: None,
        });
    };
    for (i, (block_override, state_override)) in overrides.iter().enumerate() {
        for (
            addr,
            StateOverrideObject {
                balance,
                nonce,
                code,
                storage_override,
            },
        ) in state_override.iter()
        {
            return_simulate_failure_on_err!(state_overrides.add_address_at(i, addr));

            if let Some(balance) = balance {
                return_simulate_failure_on_err!(state_overrides.set_balance_at(i, addr, balance));
            }

            if let Some(nonce) = nonce {
                return_simulate_failure_on_err!(state_overrides.set_nonce_at(
                    i,
                    addr,
                    nonce.as_limbs()[0]
                ));
            }

            if let Some(code) = code {
                return_simulate_failure_on_err!(state_overrides.set_code_at(i, addr, code));
            }

            match storage_override {
                Some(StorageOverride::State(storage_override)) => {
                    for (k, v) in storage_override {
                        return_simulate_failure_on_err!(state_overrides.set_state_at(i, addr, k, v));
                    }
                }
                Some(StorageOverride::StateDiff(override_state_diff)) => {
                    for (k, v) in override_state_diff {
                        return_simulate_failure_on_err!(
                            state_overrides.set_state_diff_at(i, addr, k, v)
                        );
                    }
                }
                None => {}
            }
        }

        let BlockOverride {
            number,
            time,
            gas_limit,
            fee_recipient,
            prev_randao,
            base_fee_per_gas,
            withdrawals,
        } = block_override;

        if let Some(number) = number {
            return_simulate_failure_on_err!(block_overrides.set_number_at(i, number.as_limbs()[0]));
        }

        if let Some(time) = time {
            return_simulate_failure_on_err!(block_overrides.set_time_at(i, time.as_limbs()[0]));
        }

        if let Some(gas_limit) = gas_limit {
            return_simulate_failure_on_err!(
                block_overrides.set_gas_limit_at(i, gas_limit.as_limbs()[0])
            );
        }

        if let Some(fee_recipient) = fee_recipient {
            return_simulate_failure_on_err!(block_overrides.set_fee_recipient_at(i, fee_recipient));
        }

        if let Some(prev_randao) = prev_randao {
            return_simulate_failure_on_err!(block_overrides.set_prev_randao_at(i, prev_randao));
        }

        if let Some(base_fee_per_gas) = base_fee_per_gas {
            return_simulate_failure_on_err!(
                block_overrides.set_base_fee_per_gas_at(i, base_fee_per_gas)
            );
        }

        for withdrawal in withdrawals {
            return_simulate_failure_on_err!(block_overrides.add_withdrawal_at(i, withdrawal));
        }
    }

    let (send, recv) = channel();
    let sender_ctx = Box::new(SenderContext { sender: send });

    unsafe {
        let sender_ctx_ptr = Box::into_raw(sender_ctx);

        let status = ffi::monad_executor_eth_simulate_submit(
            eth_call_executor.eth_call_executor,
            chain_config,
            rlp_encoded_senders.as_ptr(),
            rlp_encoded_senders.len(),
            rlp_encoded_txns.as_ptr(),
            rlp_encoded_txns.len(),
            block_number,
            rlp_encoded_block_header.as_ptr(),
            rlp_encoded_block_header.len(),
            rlp_encoded_block_id.as_ptr(),
            rlp_encoded_block_id.len(),
            rlp_encoded_grandparent_id.as_ptr(),
            rlp_encoded_grandparent_id.len(),
            gas_limit,
            max_calls,
            state_overrides.as_mut_ptr(),
            block_overrides.as_mut_ptr(),
            emit_native_transfer_logs,
            Some(eth_call_submit_callback),
            sender_ctx_ptr as *mut std::ffi::c_void,
        );
        return_simulate_failure_on_err!(ensure_executor_ok(status), {
            let _ = Box::from_raw(sender_ctx_ptr); // reclaims ownership in the event of an error status code.
        });
    }

    let result_raw = match recv.await {
        Ok(r) => r,
        Err(e) => {
            warn!("callback from eth_simulate_v1 failed: {:?}", e);

            return SimulateResult::Failure(FailureSimulateResult {
                error_code: EthCallResult::OtherError,
                message: "internal eth_simulate_v1 error".to_string(),
                data: None,
            });
        }
    };

    let Some(result) = MonadExecutorResult::from_c_handle(result_raw) else {
        warn!("callback from eth_simulate_v1 failed: result pointer is null");

        return SimulateResult::Failure(FailureSimulateResult {
            error_code: EthCallResult::OtherError,
            message: "internal eth_simulate_v1 error: result pointer is null".to_string(),
            data: None,
        });
    };

    match result.status_code() {
        ETH_CALL_SUCCESS => match result.encoded_trace() {
            Ok(output_data) => SimulateResult::Success(SuccessSimulateResult { output_data }),
            Err(()) => SimulateResult::Failure(FailureSimulateResult {
                error_code: EthCallResult::OtherError,
                message: "internal eth_simulate_v1 error: encoded trace pointer is null"
                    .to_string(),
                data: None,
            }),
        },
        _ => {
            let message = result.message();
            SimulateResult::Failure(FailureSimulateResult {
                error_code: EthCallResult::OtherError,
                message,
                data: None,
            })
        }
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
