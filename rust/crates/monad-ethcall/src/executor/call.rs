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

use std::ffi::CStr;

use alloy_consensus::{Header, Transaction as _, TxEnvelope};
use alloy_eips::eip2718::Encodable2718;
use alloy_primitives::Address;
use alloy_rlp::Encodable;
use futures::channel::oneshot::channel;
use tracing::warn;

use super::{
    decode_revert_message, eth_call_submit_callback, CallResult, EthCallResult, FailureCallResult,
    MonadExecutor, RevertCallResult, SenderContext, SuccessCallResult, ETH_CALL_SUCCESS,
    EVMC_MONAD_RESERVE_BALANCE_VIOLATION, EVMC_OUT_OF_GAS,
};
use crate::{
    ffi,
    overrides::{StateOverrideObject, StateOverrideSet, StorageOverride},
    ChainId, MonadTracer,
};

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

impl MonadExecutor {
    pub async fn eth_call(&self, request: EthCallRequest<'_>) -> CallResult {
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

        for (
            addr,
            StateOverrideObject {
                balance,
                nonce,
                code,
                storage_override,
            },
        ) in state_override_set
        {
            let addr: &[u8] = addr.as_slice();

            unsafe {
                ffi::add_override_address(override_ctx, addr.as_ptr(), addr.len());

                if let Some(balance) = balance {
                    // Big Endianness is to match with decode in eth_call.cpp (intx::be::load)
                    let balance = balance.to_be_bytes_vec();

                    ffi::set_override_balance(
                        override_ctx,
                        addr.as_ptr(),
                        addr.len(),
                        balance.as_ptr(),
                        balance.len(),
                    );
                }
                if let Some(nonce) = nonce {
                    ffi::set_override_nonce(
                        override_ctx,
                        addr.as_ptr(),
                        addr.len(),
                        nonce.as_limbs()[0],
                    )
                }

                if let Some(code) = code {
                    ffi::set_override_code(
                        override_ctx,
                        addr.as_ptr(),
                        addr.len(),
                        code.as_ptr(),
                        code.len(),
                    )
                }

                match storage_override {
                    Some(StorageOverride::State(override_state)) => {
                        for (k, v) in override_state {
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
            ffi::monad_executor_eth_call_submit(
                self.eth_call_executor,
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
                Box::into_raw(sender_ctx) as *mut std::ffi::c_void,
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
                            std::slice::from_raw_parts((*result).output_data, output_data_len)
                                .to_vec()
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
                            Err(_) => {
                                String::from("execution error eth_call message invalid utf-8")
                            }
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
}
