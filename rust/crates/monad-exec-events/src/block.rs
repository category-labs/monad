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

#[cfg(feature = "alloy")]
use itertools::Itertools;

#[cfg(feature = "alloy")]
use crate::ffi;
use crate::ffi::{
    monad_c_address, monad_c_bytes32, monad_c_eth_txn_header, monad_c_eth_txn_receipt,
    monad_c_uint256_ne, monad_exec_block_end, monad_exec_block_start, monad_exec_txn_call_frame,
};

/// Block reconstructed from execution events.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct ExecutedBlock {
    pub start: monad_exec_block_start,
    pub end: monad_exec_block_end,
    pub txns: Box<[ExecutedTxn]>,
}

#[cfg(feature = "alloy")]
impl ExecutedBlock {
    /// Creates an alloy consensus header.
    pub fn to_alloy_header(&self) -> alloy_consensus::Header {
        alloy_consensus::Header {
            parent_hash: alloy_primitives::B256::from(self.start.parent_eth_hash.bytes),
            ommers_hash: alloy_primitives::B256::from(self.start.eth_block_input.ommers_hash.bytes),
            beneficiary: alloy_primitives::Address::from(
                self.start.eth_block_input.beneficiary.bytes,
            ),
            state_root: alloy_primitives::B256::from(self.end.exec_output.state_root.bytes),
            transactions_root: alloy_primitives::B256::from(
                self.start.eth_block_input.transactions_root.bytes,
            ),
            receipts_root: alloy_primitives::B256::from(self.end.exec_output.receipts_root.bytes),
            logs_bloom: alloy_primitives::Bloom::from(self.end.exec_output.logs_bloom.bytes),
            difficulty: alloy_primitives::U256::from(self.start.eth_block_input.difficulty),
            number: self.start.eth_block_input.number,
            gas_limit: self.start.eth_block_input.gas_limit,
            gas_used: self.end.exec_output.gas_used,
            timestamp: self.start.eth_block_input.timestamp,
            extra_data: alloy_primitives::Bytes::copy_from_slice(
                &self.start.eth_block_input.extra_data.bytes
                    [0..self.start.eth_block_input.extra_data_length as usize],
            ),
            mix_hash: alloy_primitives::B256::from(self.start.eth_block_input.prev_randao.bytes),
            nonce: alloy_primitives::B64::from(self.start.eth_block_input.nonce.bytes),
            base_fee_per_gas: alloy_primitives::U256::from_limbs(
                self.start.eth_block_input.base_fee_per_gas.limbs,
            )
            .try_into()
            .ok(),
            withdrawals_root: {
                let withdrawals_root =
                    alloy_primitives::B256::from(self.start.eth_block_input.withdrawals_root.bytes);

                (!withdrawals_root.const_is_zero()).then_some(withdrawals_root)
            },
            blob_gas_used: Some(0),
            excess_blob_gas: Some(0),
            parent_beacon_block_root: Some(alloy_primitives::B256::ZERO),
            requests_hash: Some(alloy_primitives::B256::ZERO),
        }
    }

    /// Creates an alloy rpc header.
    pub fn to_alloy_rpc_header(&self) -> alloy_rpc_types::Header {
        let header = self.to_alloy_header();

        let size = header.size();

        alloy_rpc_types::Header {
            hash: alloy_primitives::FixedBytes(self.end.eth_block_hash.bytes),
            inner: header,
            total_difficulty: Some(alloy_primitives::U256::ZERO),
            size: Some(alloy_primitives::U256::from(size)),
        }
    }

    /// Creates an alloy block with a full transaction list.
    pub fn to_alloy_rpc(&self) -> alloy_rpc_types::Block {
        let header = self.to_alloy_rpc_header();

        let transactions = self
            .txns
            .iter()
            .enumerate()
            .map(|(tx_idx, tx)| {
                use alloy_consensus::{transaction::Recovered, Transaction};

                let inner = tx.to_alloy();
                let effective_gas_price = inner.effective_gas_price(header.base_fee_per_gas);
                let sender = alloy_primitives::Address::from(tx.sender.bytes);

                alloy_rpc_types::Transaction {
                    inner: Recovered::new_unchecked(inner, sender),
                    block_hash: Some(header.hash),
                    block_number: Some(header.number),
                    transaction_index: Some(tx_idx as u64),
                    effective_gas_price: Some(effective_gas_price),
                }
            })
            .collect();

        alloy_rpc_types::Block {
            header,
            uncles: Vec::default(),
            transactions: alloy_rpc_types::BlockTransactions::Full(transactions),
            withdrawals: None,
        }
    }

    /// Iterate over alloy transactions.
    pub fn iter_alloy_tx_envelopes(
        &self,
    ) -> impl Iterator<Item = alloy_consensus::TxEnvelope> + '_ {
        self.txns.iter().map(|tx| tx.to_alloy())
    }

    /// Iterate over alloy rpc transactions.
    pub fn iter_alloy_rpc_txs(&self) -> impl Iterator<Item = alloy_rpc_types::Transaction> + '_ {
        let block_hash = alloy_primitives::FixedBytes::from(self.end.eth_block_hash.bytes);
        let block_number = self.start.eth_block_input.number;

        let base_fee = Some(
            TryInto::<u64>::try_into(alloy_primitives::U256::from_limbs(
                self.start.eth_block_input.base_fee_per_gas.limbs,
            ))
            .expect("base fee fits in u64"),
        );

        self.txns.iter().enumerate().map(move |(tx_idx, tx)| {
            let transaction_index = Some(tx_idx as u64);

            let tx = tx.to_alloy_recovered();

            let effective_gas_price =
                alloy_consensus::Transaction::effective_gas_price(tx.inner(), base_fee);

            alloy_rpc_types::Transaction {
                inner: tx,
                block_hash: Some(block_hash),
                block_number: Some(block_number),
                transaction_index,
                effective_gas_price: Some(effective_gas_price),
            }
        })
    }

    /// Iterate over alloy rpc transaction receipts.
    pub fn iter_alloy_rpc_tx_receipts(
        &self,
    ) -> impl Iterator<Item = alloy_rpc_types::TransactionReceipt> + '_ {
        let block_hash = Some(alloy_primitives::FixedBytes::from(
            self.end.eth_block_hash.bytes,
        ));
        let block_number = Some(self.start.eth_block_input.number);
        let block_timestamp = Some(self.start.eth_block_input.timestamp);

        let base_fee = Some(
            TryInto::<u64>::try_into(alloy_primitives::U256::from_limbs(
                self.start.eth_block_input.base_fee_per_gas.limbs,
            ))
            .expect("base fee fits in u64"),
        );

        let mut cumulative_gas_used = 0u64;
        let mut log_index = 0u64;

        self.txns.iter().enumerate().map(move |(tx_idx, tx)| {
            cumulative_gas_used += tx.receipt.gas_used;

            let transaction_hash = alloy_primitives::FixedBytes(tx.hash.bytes);
            let transaction_index = Some(tx_idx as u64);

            let logs = tx
                .iter_alloy_logs()
                .map(|log| {
                    let log = alloy_rpc_types::Log {
                        inner: log,
                        block_hash,
                        block_number,
                        block_timestamp,
                        transaction_hash: Some(transaction_hash),
                        transaction_index,
                        log_index: Some(log_index),
                        removed: false,
                    };

                    log_index += 1;

                    log
                })
                .collect_vec();

            let logs_bloom = alloy_primitives::logs_bloom(logs.iter().map(|log| &log.inner));

            let receipt_with_bloom = alloy_consensus::ReceiptWithBloom {
                receipt: alloy_consensus::Receipt {
                    status: alloy_consensus::Eip658Value::Eip658(tx.receipt.status),
                    cumulative_gas_used,
                    logs,
                },
                logs_bloom,
            };

            let receipt = match tx.header.txn_type {
                ffi::MONAD_TXN_LEGACY => {
                    alloy_consensus::ReceiptEnvelope::Legacy(receipt_with_bloom)
                }
                ffi::MONAD_TXN_EIP2930 => {
                    alloy_consensus::ReceiptEnvelope::Eip2930(receipt_with_bloom)
                }
                ffi::MONAD_TXN_EIP1559 => {
                    alloy_consensus::ReceiptEnvelope::Eip1559(receipt_with_bloom)
                }
                ffi::MONAD_TXN_EIP4844 => {
                    unreachable!("ExecutedTxn encountered unsupported EIP4844 tx type");
                }
                ffi::MONAD_TXN_EIP7702 => {
                    alloy_consensus::ReceiptEnvelope::Eip7702(receipt_with_bloom)
                }
                _ => panic!(
                    "ExecutedTxn encountered unknown tx type {}",
                    tx.header.txn_type
                ),
            };

            let from = alloy_primitives::Address::from(tx.sender.bytes);

            let (to, contract_address) = if tx.header.is_contract_creation {
                (None, Some(from.create(tx.header.nonce)))
            } else {
                (
                    Some(alloy_primitives::Address::from(tx.header.to.bytes)),
                    None,
                )
            };

            alloy_rpc_types::TransactionReceipt {
                inner: receipt,
                transaction_hash,
                transaction_index,
                block_hash,
                block_number,
                gas_used: tx.receipt.gas_used,
                // TODO(andr-dev): Don't build TxEnvelope just to calculate effective gas price
                effective_gas_price: alloy_consensus::Transaction::effective_gas_price(
                    &tx.to_alloy(),
                    base_fee,
                ),
                blob_gas_used: None,
                blob_gas_price: None,
                from,
                to,
                contract_address,
            }
        })
    }

    /// Creates a flat list of alloy logs including all logs in the block's transactions.
    pub fn get_alloy_rpc_logs(&self) -> Vec<alloy_rpc_types::Log> {
        self.txns
            .iter()
            .enumerate()
            .flat_map(|(tx_idx, tx)| {
                tx.to_alloy_logs()
                    .into_iter()
                    .map(move |log| (tx_idx, &tx.hash, log))
            })
            .enumerate()
            .map(|(log_idx, (tx_idx, tx_hash, log))| alloy_rpc_types::Log {
                inner: log,
                block_hash: Some(alloy_primitives::FixedBytes::from(
                    self.end.eth_block_hash.bytes,
                )),
                block_number: Some(self.start.eth_block_input.number),
                block_timestamp: Some(self.start.eth_block_input.timestamp),
                transaction_hash: Some(alloy_primitives::FixedBytes::from(tx_hash.bytes)),
                transaction_index: Some(tx_idx as u64),
                log_index: Some(log_idx as u64),
                // TODO(andr-dev): Revisit
                removed: false,
            })
            .collect()
    }
}

/// Transaction reconstructed from execution events.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct ExecutedTxn {
    pub hash: monad_c_bytes32,
    pub sender: monad_c_address,
    pub header: monad_c_eth_txn_header,
    pub input: Box<[u8]>,
    pub access_list: Box<[ExecutedTxnAccessListEntry]>,
    pub authorization_list: Box<[ExecutedTxnSignedAuthorization]>,
    pub receipt: monad_c_eth_txn_receipt,
    pub logs: Box<[ExecutedTxnLog]>,
    pub call_frames: Option<Box<[ExecutedTxnCallFrame]>>,
}

#[cfg(feature = "alloy")]
impl ExecutedTxn {
    /// Creates an alloy tx envelope.
    pub fn to_alloy(&self) -> alloy_consensus::TxEnvelope {
        let to = if self.header.is_contract_creation {
            alloy_primitives::TxKind::Create
        } else {
            alloy_primitives::TxKind::Call(alloy_primitives::Address::from(self.header.to.bytes))
        };

        let txn_signature = alloy_primitives::Signature::from_scalars_and_parity(
            alloy_primitives::B256::from(alloy_primitives::U256::from_limbs(self.header.r.limbs)),
            alloy_primitives::B256::from(alloy_primitives::U256::from_limbs(self.header.s.limbs)),
            self.header.y_parity,
        );

        let txn_hash = alloy_primitives::TxHash::from(self.hash.bytes);

        let chain_id = TryInto::<u64>::try_into(alloy_primitives::U256::from_limbs(
            self.header.chain_id.limbs,
        ))
        .unwrap();
        let gas_price = TryInto::<u128>::try_into(alloy_primitives::U256::from_limbs(
            self.header.max_fee_per_gas.limbs,
        ))
        .unwrap();
        let value = alloy_primitives::U256::from_limbs(self.header.value.limbs);
        let input = alloy_primitives::Bytes::copy_from_slice(&self.input);

        let access_list = alloy_rpc_types::AccessList(
            self.access_list
                .iter()
                .map(
                    |ExecutedTxnAccessListEntry {
                         address,
                         storage_keys,
                     }| alloy_rpc_types::AccessListItem {
                        address: alloy_primitives::Address::from(address.bytes),
                        storage_keys: storage_keys
                            .iter()
                            .map(|storage_key| alloy_primitives::FixedBytes(storage_key.bytes))
                            .collect(),
                    },
                )
                .collect_vec(),
        );

        let authorization_list = self
            .authorization_list
            .iter()
            .map(
                |ExecutedTxnSignedAuthorization {
                     chain_id,
                     address,
                     nonce,

                     y_parity,
                     r,
                     s,
                 }| {
                    alloy_eips::eip7702::SignedAuthorization::new_unchecked(
                        alloy_eips::eip7702::Authorization {
                            chain_id: alloy_primitives::U256::from_limbs(chain_id.limbs),
                            address: alloy_primitives::Address(alloy_primitives::FixedBytes(
                                address.bytes,
                            )),
                            nonce: *nonce,
                        },
                        if *y_parity { 1 } else { 0 },
                        alloy_primitives::U256::from_limbs(r.limbs),
                        alloy_primitives::U256::from_limbs(s.limbs),
                    )
                },
            )
            .collect_vec();

        match self.header.txn_type {
            ffi::MONAD_TXN_LEGACY => {
                alloy_consensus::TxEnvelope::Legacy(alloy_consensus::Signed::new_unchecked(
                    alloy_consensus::TxLegacy {
                        chain_id: (chain_id != 0).then_some(chain_id),
                        nonce: self.header.nonce,
                        gas_price,
                        gas_limit: self.header.gas_limit,
                        to,
                        value,
                        input,
                    },
                    txn_signature,
                    txn_hash,
                ))
            }
            ffi::MONAD_TXN_EIP2930 => {
                alloy_consensus::TxEnvelope::Eip2930(alloy_consensus::Signed::new_unchecked(
                    alloy_consensus::TxEip2930 {
                        chain_id,
                        nonce: self.header.nonce,
                        gas_price,
                        gas_limit: self.header.gas_limit,
                        to,
                        value,
                        access_list,
                        input,
                    },
                    txn_signature,
                    txn_hash,
                ))
            }
            ffi::MONAD_TXN_EIP1559 => {
                alloy_consensus::TxEnvelope::Eip1559(alloy_consensus::Signed::new_unchecked(
                    alloy_consensus::TxEip1559 {
                        chain_id,
                        nonce: self.header.nonce,
                        gas_limit: self.header.gas_limit,
                        max_fee_per_gas: gas_price,
                        max_priority_fee_per_gas: alloy_primitives::U256::from_limbs(
                            self.header.max_priority_fee_per_gas.limbs,
                        )
                        .try_into()
                        .unwrap(),
                        to,
                        value,
                        access_list,
                        input,
                    },
                    txn_signature,
                    txn_hash,
                ))
            }
            ffi::MONAD_TXN_EIP4844 => {
                unreachable!("ExecutedTxn encountered unsupported EIP4844 tx type");
            }
            ffi::MONAD_TXN_EIP7702 => {
                alloy_consensus::TxEnvelope::Eip7702(alloy_consensus::Signed::new_unchecked(
                    alloy_consensus::TxEip7702 {
                        chain_id,
                        nonce: self.header.nonce,
                        gas_limit: self.header.gas_limit,
                        max_fee_per_gas: alloy_primitives::U256::from_limbs(
                            self.header.max_fee_per_gas.limbs,
                        )
                        .try_into()
                        .unwrap(),
                        max_priority_fee_per_gas: alloy_primitives::U256::from_limbs(
                            self.header.max_priority_fee_per_gas.limbs,
                        )
                        .try_into()
                        .unwrap(),
                        to: alloy_primitives::Address::from(self.header.to.bytes),
                        value,
                        access_list,
                        authorization_list,
                        input,
                    },
                    txn_signature,
                    txn_hash,
                ))
            }
            _ => panic!(
                "ExecutedTxn encountered unknown tx type {}",
                self.header.txn_type
            ),
        }
    }

    /// Creates a recovered alloy tx envelope.
    pub fn to_alloy_recovered(
        &self,
    ) -> alloy_consensus::transaction::Recovered<alloy_consensus::TxEnvelope> {
        alloy_consensus::transaction::Recovered::new_unchecked(
            self.to_alloy(),
            alloy_primitives::Address::from(self.sender.bytes),
        )
    }

    /// Iterate over alloy logs.
    pub fn iter_alloy_logs(&self) -> impl Iterator<Item = alloy_primitives::Log> + '_ {
        self.logs.iter().map(ExecutedTxnLog::to_alloy)
    }

    /// Creates a list of alloy logs.
    pub fn to_alloy_logs(&self) -> Vec<alloy_primitives::Log> {
        self.iter_alloy_logs().collect_vec()
    }
}

/// Transaction log reconstructed from execution events.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct ExecutedTxnLog {
    pub address: monad_c_address,
    pub topic: Box<[monad_c_bytes32]>,
    pub data: Box<[u8]>,
}

#[cfg(feature = "alloy")]
impl ExecutedTxnLog {
    /// Creates an alloy log.
    pub fn to_alloy(&self) -> alloy_primitives::Log {
        alloy_primitives::Log {
            address: alloy_primitives::Address::from(self.address.bytes),
            data: alloy_primitives::LogData::new_unchecked(
                self.topic
                    .iter()
                    .map(|bytes| alloy_primitives::B256::from(bytes.bytes))
                    .collect(),
                alloy_primitives::Bytes::copy_from_slice(&self.data),
            ),
        }
    }
}

/// Transaction call frame reconstructed from execution events.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct ExecutedTxnCallFrame {
    pub call_frame: monad_exec_txn_call_frame,
    pub input: Box<[u8]>,
    pub r#return: Box<[u8]>,
}

/// Access List entry reconstructed from execution events.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct ExecutedTxnAccessListEntry {
    pub address: monad_c_address,
    pub storage_keys: Box<[monad_c_bytes32]>,
}

/// Authorization reconstructed from execution events.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct ExecutedTxnSignedAuthorization {
    pub chain_id: monad_c_uint256_ne,
    pub address: monad_c_address,
    pub nonce: u64,

    pub y_parity: bool,
    pub r: monad_c_uint256_ne,
    pub s: monad_c_uint256_ne,
}
