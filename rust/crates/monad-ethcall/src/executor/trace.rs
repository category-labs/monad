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

use alloy_consensus::Header;
use alloy_rlp::Encodable;
use futures::channel::oneshot::channel;
use tracing::{error, warn};

use super::{
    eth_call_submit_callback, CallResult, EthCallResult, FailureCallResult, MonadExecutor,
    SenderContext, SuccessCallResult, ETH_CALL_SUCCESS,
};
use crate::{ffi, ChainId, MonadTracer};

impl MonadExecutor {
    pub async fn eth_trace_block_or_transaction(
        &self,
        chain_id: ChainId,
        block_header: Header,
        block_number: u64,
        block_id: Option<[u8; 32]>,
        parent_id: Option<[u8; 32]>,
        grandparent_id: Option<[u8; 32]>,
        transaction_index: i64,
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
            ffi::monad_executor_run_transactions(
                self.eth_call_executor,
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
                Box::into_raw(sender_ctx) as *mut std::ffi::c_void,
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
}
