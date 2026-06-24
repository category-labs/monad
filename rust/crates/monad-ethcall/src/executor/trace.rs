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

use alloy_consensus::Header;
use alloy_rlp::Encodable;
use futures::channel::oneshot::channel;
use tracing::warn;

use super::{
    eth_call_submit_callback, MessageError, MonadExecutor, SenderContext, ETH_CALL_SUCCESS,
};
use crate::{ffi, ChainId, MonadExecutorResult, MonadTracer};

#[derive(Clone, Debug)]
pub struct EthTraceSuccess {
    pub output_data: Box<[u8]>,
}

#[derive(Clone, Debug)]
pub enum EthTraceError {
    InternalError,
    Other(String),
}

impl MonadExecutor {
    #[allow(clippy::too_many_arguments)]
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
    ) -> Result<EthTraceSuccess, EthTraceError> {
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

        let result_raw = recv.await.map_err(|e| {
            warn!(
                "callback from `eth_trace_block_or_transaction` failed: {:?}",
                e
            );

            EthTraceError::InternalError
        })?;

        let result = MonadExecutorResult::from_c_handle(result_raw).ok_or_else(|| {
            warn!("execution error `eth_trace_block_or_transaction` returned null result");

            EthTraceError::InternalError
        })?;

        let call_result = match result.status_code() {
            ETH_CALL_SUCCESS => {
                let output_data = result.encoded_trace().map_err(|_| {
                    warn!("execution error `eth_trace_block_or_transaction` failed: encoded trace pointer is null");

                    EthTraceError::InternalError
                })?;

                Ok(EthTraceSuccess { output_data })
            }
            _ => {
                let message = result.message().map_err(|e| {
                    match e {
                        MessageError::NullPointerError => {
                            warn!("execution error `eth_trace_block_or_transaction` failed: message pointer is null");
                        }
                        MessageError::InvalidUtf8Error => {
                            warn!("execution error `eth_trace_block_or_transaction` failed: message pointer is invalid utf-8");
                        }
                    }
                    EthTraceError::InternalError
                })?;
                Err(EthTraceError::Other(message))
            }
        };

        call_result
    }
}
