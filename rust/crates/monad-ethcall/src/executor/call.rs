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

use alloy_consensus::{Header, Transaction as _, TxEnvelope};
use alloy_eips::eip2718::Encodable2718;
use alloy_primitives::Address;
use alloy_rlp::Encodable;
use futures::channel::oneshot::channel;
use tracing::warn;

use super::{
    decode_revert_message, eth_call_submit_callback, EthCallResult, MessageError, MonadExecutor,
    MonadExecutorResult, SenderContext, ETH_CALL_SUCCESS, EVMC_MONAD_RESERVE_BALANCE_VIOLATION,
    EVMC_OUT_OF_GAS,
};
use crate::{
    ffi,
    overrides::{StateOverrideObject, StateOverrideSet, StorageOverride},
    ChainId, MonadTracer,
};

#[derive(Clone, Debug)]
pub struct EthCallSuccess {
    pub gas_used: u64,
    pub gas_refund: u64,
    // We interpret this as rlp encoded CallFrames for debug_traceCall
    pub output_data: Box<[u8]>,
}

#[derive(Clone, Debug)]
pub enum EthCallError {
    Failure {
        error_code: EthCallResult,
        gas_used: u64,
        gas_refund: u64,
        message: String,
        data: Option<String>,
    },
    GasLimitTooHigh,
    InternalError,
    Other {
        message: String,
    },
    ReserveBalanceViolation {
        gas_used: u64,
        gas_refund: u64,
    },
    Trace {
        trace: Box<[u8]>,
    },
}

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
    pub async fn eth_call(
        &self,
        request: EthCallRequest<'_>,
    ) -> Result<EthCallSuccess, EthCallError> {
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
            return Err(EthCallError::GasLimitTooHigh);
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

        let result_raw = recv.await.map_err(|e| {
            unsafe { ffi::monad_state_override_destroy(override_ctx) };

            warn!("callback from `eth_call` failed: {:?}", e);

            EthCallError::InternalError
        })?;

        let result = MonadExecutorResult::from_c_handle(result_raw).ok_or_else(|| {
            unsafe { ffi::monad_state_override_destroy(override_ctx) };

            warn!("execution error `eth_call` failed: returned null result");

            EthCallError::InternalError
        })?;

        let tracer_cval: u32 = tracer.into();

        let call_result = match result.status_code() {
            ETH_CALL_SUCCESS => {
                let output_data = if tracer_cval == ffi::monad_tracer_config_NOOP_TRACER {
                    result.output_data().map_err(|_| {
                        unsafe { ffi::monad_state_override_destroy(override_ctx) };

                        warn!("execution error `eth_call` failed: output data pointer is null");

                        EthCallError::InternalError
                    })?
                } else {
                    result.encoded_trace().map_err(|_| {
                        unsafe { ffi::monad_state_override_destroy(override_ctx) };

                        warn!("execution error `eth_call` failed: encoded trace pointer is null");

                        EthCallError::InternalError
                    })?
                };

                Ok(EthCallSuccess {
                    gas_used: result.gas_used(),
                    gas_refund: result.gas_refund(),
                    output_data,
                })
            }
            EVMC_MONAD_RESERVE_BALANCE_VIOLATION => {
                if tracer_cval == ffi::monad_tracer_config_NOOP_TRACER {
                    Err(EthCallError::ReserveBalanceViolation {
                        gas_used: result.gas_used(),
                        gas_refund: result.gas_refund(),
                    })
                } else {
                    let trace = result.encoded_trace().map_err(|_| {
                        unsafe { ffi::monad_state_override_destroy(override_ctx) };

                        warn!("execution error `eth_call` failed: encoded trace pointer is null");

                        EthCallError::InternalError
                    })?;
                    Err(EthCallError::Trace { trace })
                }
            }
            _ => {
                if result.is_message_null() {
                    // This means execution reverted, not a validation error
                    if tracer_cval == ffi::monad_tracer_config_NOOP_TRACER {
                        let output_data = result.output_data().map_err(|_| {
                            unsafe { ffi::monad_state_override_destroy(override_ctx) };

                            warn!("execution error `eth_call` failed: output data pointer is null");

                            EthCallError::InternalError
                        })?;
                        let message = String::from("execution reverted");
                        let formatted_message = match decode_revert_message(&output_data) {
                            Some(error_message) => format!("{}: {}", message, error_message),
                            None => message,
                        };
                        Err(EthCallError::Failure {
                            error_code: if result.status_code() == EVMC_OUT_OF_GAS {
                                EthCallResult::OutOfGas
                            } else {
                                EthCallResult::ExecutionError
                            },
                            gas_used: result.gas_used(),
                            gas_refund: result.gas_refund(),
                            message: formatted_message,
                            data: Some(format!("0x{}", hex::encode(&output_data))),
                        })
                    } else {
                        let trace = result.encoded_trace().map_err(|_| {
                            unsafe { ffi::monad_state_override_destroy(override_ctx) };

                            warn!(
                                "execution error `eth_call` failed: encoded trace pointer is null"
                            );

                            EthCallError::InternalError
                        })?;
                        Err(EthCallError::Trace { trace })
                    }
                } else {
                    // This means we hit a validation error (execution not started)
                    let message = result.message().map_err(|e| {
                        unsafe { ffi::monad_state_override_destroy(override_ctx) };
                        match e {
                            MessageError::NullPointerError => {
                                warn!("execution error `eth_call` failed: message pointer is null");
                            }
                            MessageError::InvalidUtf8Error => {
                                warn!("execution error `eth_call` failed: message pointer is invalid utf-8");
                            }
                        }
                        EthCallError::InternalError
                    })?;
                    Err(EthCallError::Other { message })
                }
            }
        };

        unsafe {
            ffi::monad_state_override_destroy(override_ctx);
        }

        call_result
    }
}
