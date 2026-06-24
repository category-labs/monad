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

use alloy_consensus::{Header, TxEnvelope};
use alloy_primitives::Address;
use alloy_rlp::Encodable;
use futures::channel::oneshot::channel;
use tracing::warn;

use super::{
    eth_call_submit_callback, MessageError, MonadExecutor, MonadExecutorResult, SenderContext,
    ETH_CALL_SUCCESS,
};
use crate::{
    ffi,
    overrides::{
        BlockOverride, CBlockOverrideVec, CStateOverrideVec, StateOverrideObject, StateOverrideSet,
        StorageOverride,
    },
    ChainId,
};

#[derive(Clone, Debug)]
pub struct EthSimulateSuccess {
    pub output_data: Box<[u8]>,
}

#[derive(Clone, Debug)]
pub enum EthSimulateError {
    BlockOverrideFailure,
    InternalError,
    StateOverrideFailure,
    InputSizeMismatch,
    Other(String),
}

impl MonadExecutor {
    #[allow(clippy::too_many_arguments)]
    pub async fn eth_simulate_v1(
        &self,
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
        overrides: &[(&BlockOverride, &StateOverrideSet)],
    ) -> Result<EthSimulateSuccess, EthSimulateError> {
        if (calls.len() != overrides.len()) || (calls.len() != senders.len()) {
            return Err(EthSimulateError::InputSizeMismatch);
        }

        for (txs, senders) in calls.iter().zip(senders.iter()) {
            if txs.len() != senders.len() {
                return Err(EthSimulateError::InputSizeMismatch);
            }
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

            return Err(EthSimulateError::StateOverrideFailure);
        };
        let Some(mut block_overrides) = CBlockOverrideVec::with_capacity(calls.len()) else {
            warn!("failed to create block override vector");

            return Err(EthSimulateError::BlockOverrideFailure);
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
                state_overrides.add_address_at(i, addr);

                if let Some(balance) = balance {
                    state_overrides.set_balance_at(i, addr, balance);
                }

                if let Some(nonce) = nonce {
                    state_overrides.set_nonce_at(i, addr, nonce.as_limbs()[0]);
                }

                if let Some(code) = code {
                    state_overrides.set_code_at(i, addr, code)
                }

                match storage_override {
                    Some(StorageOverride::State(storage_override)) => {
                        for (k, v) in storage_override {
                            state_overrides.set_state_at(i, addr, k, v)
                        }
                    }
                    Some(StorageOverride::StateDiff(override_state_diff)) => {
                        for (k, v) in override_state_diff {
                            state_overrides.set_state_diff_at(i, addr, k, v)
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
                block_overrides.set_number_at(i, number.as_limbs()[0]);
            }

            if let Some(time) = time {
                block_overrides.set_time_at(i, time.as_limbs()[0]);
            }

            if let Some(gas_limit) = gas_limit {
                block_overrides.set_gas_limit_at(i, gas_limit.as_limbs()[0]);
            }

            if let Some(fee_recipient) = fee_recipient {
                block_overrides.set_fee_recipient_at(i, fee_recipient);
            }

            if let Some(prev_randao) = prev_randao {
                block_overrides.set_prev_randao_at(i, prev_randao);
            }

            if let Some(base_fee_per_gas) = base_fee_per_gas {
                block_overrides.set_base_fee_per_gas_at(i, base_fee_per_gas);
            }

            for withdrawal in withdrawals {
                block_overrides.add_withdrawal_at(i, withdrawal);
            }
        }

        let (send, recv) = channel();
        let sender_ctx = Box::new(SenderContext { sender: send });

        unsafe {
            ffi::monad_executor_eth_simulate_submit(
                self.eth_call_executor,
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
                Box::into_raw(sender_ctx) as *mut std::ffi::c_void,
            );
        }

        let result_raw = recv.await.map_err(|e| {
            warn!("callback from `eth_simulate_v1` failed: {:?}", e);
            EthSimulateError::InternalError
        })?;

        let Some(result) = MonadExecutorResult::from_c_handle(result_raw) else {
            warn!("execution error `eth_simulate_v1` failed: result pointer is null");
            return Err(EthSimulateError::InternalError);
        };

        match result.status_code() {
            ETH_CALL_SUCCESS => {
                let output_data = result.encoded_trace().map_err(|_| {
                    warn!(
                        "execution error `eth_simulate_v1` failed: encoded trace pointer is null"
                    );
                    EthSimulateError::InternalError
                })?;
                Ok(EthSimulateSuccess { output_data })
            }
            _ => {
                let message = result.message().map_err(|e| {
                    match e {
                        MessageError::NullPointerError => {
                            warn!("execution error `eth_simulate_v1` failed: message pointer is null");
                        }
                        MessageError::InvalidUtf8Error => {
                            warn!("execution error `eth_simulate_v1` failed: message pointer is invalid utf-8");
                        }
                    }
                    EthSimulateError::InternalError
                })?;
                Err(EthSimulateError::Other(message))
            }
        }
    }
}
