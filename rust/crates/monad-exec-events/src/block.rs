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
    monad_address, monad_bytes32, monad_c_eth_txn_header, monad_c_eth_txn_receipt,
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
            block_access_list_hash: Some(alloy_primitives::B256::ZERO),
            slot_number: Some(self.start.round),
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
    pub fn to_alloy_rpc(&self) -> monad_transaction::rpc::Block {
        let header = self.to_alloy_rpc_header();

        let transactions = self
            .txns
            .iter()
            .enumerate()
            .map(|(tx_idx, tx)| {
                use alloy_consensus::transaction::Recovered;

                let inner = tx.to_alloy();
                let effective_gas_price = inner.effective_gas_price(header.base_fee_per_gas);
                let sender = alloy_primitives::Address::from(tx.sender.bytes);

                monad_transaction::rpc::Transaction {
                    inner: Recovered::new_unchecked(inner, sender),
                    block_hash: Some(header.hash),
                    block_number: Some(header.number),
                    block_timestamp: Some(header.timestamp),
                    transaction_index: Some(tx_idx as u64),
                    effective_gas_price: Some(effective_gas_price),
                }
            })
            .collect();

        monad_transaction::rpc::Block {
            header,
            uncles: Vec::default(),
            transactions: alloy_rpc_types::BlockTransactions::Full(transactions),
            withdrawals: None,
        }
    }

    /// Iterate over alloy transactions.
    pub fn iter_alloy_tx_envelopes(
        &self,
    ) -> impl Iterator<Item = monad_transaction::TxEnvelope> + '_ {
        self.txns.iter().map(|tx| tx.to_alloy())
    }

    /// Iterate over alloy rpc transactions.
    pub fn iter_alloy_rpc_txs(
        &self,
    ) -> impl Iterator<Item = monad_transaction::rpc::Transaction> + '_ {
        let block_hash = alloy_primitives::FixedBytes::from(self.end.eth_block_hash.bytes);
        let block_number = self.start.eth_block_input.number;
        let block_timestamp = self.start.eth_block_input.timestamp;

        let base_fee = Some(
            TryInto::<u64>::try_into(alloy_primitives::U256::from_limbs(
                self.start.eth_block_input.base_fee_per_gas.limbs,
            ))
            .expect("base fee fits in u64"),
        );

        self.txns.iter().enumerate().map(move |(tx_idx, tx)| {
            let transaction_index = Some(tx_idx as u64);

            let tx = tx.to_alloy_recovered();

            let effective_gas_price = tx.inner().effective_gas_price(base_fee);

            monad_transaction::rpc::Transaction {
                inner: tx,
                block_hash: Some(block_hash),
                block_number: Some(block_number),
                block_timestamp: Some(block_timestamp),
                transaction_index,
                effective_gas_price: Some(effective_gas_price),
            }
        })
    }

    /// Iterate over alloy rpc transaction receipts.
    pub fn iter_alloy_rpc_tx_receipts(
        &self,
    ) -> impl Iterator<Item = monad_transaction::rpc::TransactionReceipt> + '_ {
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
                    monad_transaction::ReceiptEnvelope::Legacy(receipt_with_bloom)
                }
                ffi::MONAD_TXN_EIP2930 => {
                    monad_transaction::ReceiptEnvelope::Eip2930(receipt_with_bloom)
                }
                ffi::MONAD_TXN_EIP1559 => {
                    monad_transaction::ReceiptEnvelope::Eip1559(receipt_with_bloom)
                }
                ffi::MONAD_TXN_EIP4844 => {
                    unreachable!("ExecutedTxn encountered unsupported EIP4844 tx type");
                }
                ffi::MONAD_TXN_EIP7702 => {
                    monad_transaction::ReceiptEnvelope::Eip7702(receipt_with_bloom)
                }
                ffi::MONAD_TXN_MONAD => {
                    monad_transaction::ReceiptEnvelope::Monad(receipt_with_bloom)
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

            monad_transaction::rpc::TransactionReceipt {
                inner: receipt,
                transaction_hash,
                transaction_index,
                block_hash,
                block_number,
                gas_used: tx.receipt.gas_used,
                // TODO(andr-dev): Don't build TxEnvelope just to calculate effective gas price
                effective_gas_price: tx.to_alloy().effective_gas_price(base_fee),
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
    pub hash: monad_bytes32,
    pub sender: monad_address,
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
    pub fn to_alloy(&self) -> monad_transaction::TxEnvelope {
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

        let gas_price = alloy_primitives::U256::from_limbs(self.header.max_fee_per_gas.limbs);
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
                        *y_parity,
                        alloy_primitives::U256::from_limbs(r.limbs),
                        alloy_primitives::U256::from_limbs(s.limbs),
                    )
                },
            )
            .collect_vec();

        if self.header.txn_type == ffi::MONAD_TXN_MONAD {
            assert!(self.header.monad_access_list_present <= 1);
            assert!(self.authorization_list.is_empty());
            assert!(self.header.monad_access_list_present != 0 || access_list.is_empty());
            let tx = monad_transaction::TxMonad {
                chain_id: alloy_primitives::U256::from_limbs(self.header.chain_id.limbs),
                nonce: self.header.nonce,
                gas_limit: self.header.gas_limit,
                max_fee_per_gas: gas_price,
                max_priority_fee_per_gas: alloy_primitives::U256::from_limbs(
                    self.header.max_priority_fee_per_gas.limbs,
                ),
                to,
                value,
                input,
                access_list: (self.header.monad_access_list_present != 0).then_some(access_list),
            }
            .into_signed(txn_signature);
            assert_eq!(
                *tx.hash(),
                txn_hash,
                "native event transaction commitment mismatch"
            );
            return monad_transaction::TxEnvelope::Monad(tx);
        }

        let chain_id = TryInto::<u64>::try_into(alloy_primitives::U256::from_limbs(
            self.header.chain_id.limbs,
        ))
        .unwrap();
        match self.header.txn_type {
            ffi::MONAD_TXN_LEGACY => {
                monad_transaction::TxEnvelope::Legacy(alloy_consensus::Signed::new_unchecked(
                    alloy_consensus::TxLegacy {
                        chain_id: (chain_id != 0).then_some(chain_id),
                        nonce: self.header.nonce,
                        gas_price: gas_price
                            .try_into()
                            .expect("Ethereum gas price fits in u128"),
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
                monad_transaction::TxEnvelope::Eip2930(alloy_consensus::Signed::new_unchecked(
                    alloy_consensus::TxEip2930 {
                        chain_id,
                        nonce: self.header.nonce,
                        gas_price: gas_price
                            .try_into()
                            .expect("Ethereum gas price fits in u128"),
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
                monad_transaction::TxEnvelope::Eip1559(alloy_consensus::Signed::new_unchecked(
                    alloy_consensus::TxEip1559 {
                        chain_id,
                        nonce: self.header.nonce,
                        gas_limit: self.header.gas_limit,
                        max_fee_per_gas: gas_price
                            .try_into()
                            .expect("Ethereum fee cap fits in u128"),
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
                monad_transaction::TxEnvelope::Eip7702(alloy_consensus::Signed::new_unchecked(
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
    ) -> alloy_consensus::transaction::Recovered<monad_transaction::TxEnvelope> {
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
    pub address: monad_address,
    pub topic: Box<[monad_bytes32]>,
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
    pub address: monad_address,
    pub storage_keys: Box<[monad_bytes32]>,
}

/// Authorization reconstructed from execution events.
#[allow(missing_docs)]
#[derive(Clone, Debug)]
pub struct ExecutedTxnSignedAuthorization {
    pub chain_id: monad_c_uint256_ne,
    pub address: monad_address,
    pub nonce: u64,

    pub y_parity: u8,
    pub r: monad_c_uint256_ne,
    pub s: monad_c_uint256_ne,
}

#[cfg(all(test, feature = "alloy"))]
mod native_tests {
    use alloy_eips::{Decodable2718, Encodable2718};
    use alloy_primitives::U256;
    use monad_transaction::TxEnvelope;

    use super::*;

    fn quantity(value: U256) -> monad_c_uint256_ne {
        monad_c_uint256_ne {
            limbs: value.into_limbs(),
        }
    }

    #[test]
    fn native_event_projection_preserves_sdk_commitments_and_rpc_fields() {
        let vectors: serde_json::Value = serde_json::from_str(include_str!(
            "../../../../category/execution/ethereum/core/test/monad_type40_vectors.json"
        ))
        .unwrap();
        for vector in vectors["vectors"].as_array().unwrap() {
            let bytes = hex::decode(
                vector["canonical"]
                    .as_str()
                    .unwrap()
                    .trim_start_matches("0x"),
            )
            .unwrap();
            let envelope = TxEnvelope::decode_2718_exact(&bytes).unwrap();
            let signed = envelope.as_monad().unwrap();
            let tx = signed.tx();
            let header = monad_c_eth_txn_header {
                txn_type: ffi::MONAD_TXN_MONAD,
                monad_access_list_present: u8::from(tx.access_list.is_some()),
                chain_id: quantity(tx.chain_id),
                nonce: tx.nonce,
                gas_limit: tx.gas_limit,
                max_fee_per_gas: quantity(tx.max_fee_per_gas),
                max_priority_fee_per_gas: quantity(tx.max_priority_fee_per_gas),
                value: quantity(tx.value),
                to: monad_address {
                    bytes: envelope.to().unwrap_or_default().into_array(),
                },
                is_contract_creation: tx.to.is_create(),
                r: quantity(signed.signature().r()),
                s: quantity(signed.signature().s()),
                y_parity: signed.signature().v(),
                max_fee_per_blob_gas: quantity(U256::ZERO),
                data_length: tx.input.len() as u32,
                blob_versioned_hash_length: 0,
                access_list_count: tx.access_list.as_ref().map_or(0, |list| list.len() as u32),
                auth_list_count: 0,
            };
            let event = ExecutedTxn {
                header,
                hash: monad_bytes32 {
                    bytes: envelope.hash().0,
                },
                sender: monad_address {
                    bytes: envelope.recover_signer().unwrap().into_array(),
                },
                input: tx.input.to_vec().into_boxed_slice(),
                access_list: tx
                    .access_list
                    .iter()
                    .flat_map(|list| list.iter())
                    .map(|item| ExecutedTxnAccessListEntry {
                        address: monad_address {
                            bytes: item.address.into_array(),
                        },
                        storage_keys: item
                            .storage_keys
                            .iter()
                            .map(|key| monad_bytes32 { bytes: key.0 })
                            .collect(),
                    })
                    .collect(),
                authorization_list: Box::default(),
                receipt: monad_c_eth_txn_receipt {
                    status: true,
                    log_count: 0,
                    gas_used: 21000,
                },
                logs: Box::default(),
                call_frames: None,
            };
            assert_eq!(event.to_alloy().encoded_2718(), bytes, "{}", vector["name"]);
            assert_eq!(
                event.to_alloy_recovered().signer().as_slice(),
                &event.sender.bytes
            );
            let rpc = monad_transaction::rpc::Transaction {
                inner: event.to_alloy_recovered(),
                effective_gas_price: Some(envelope.effective_gas_price(Some(1))),
                ..Default::default()
            };
            let json = serde_json::to_value(rpc).unwrap();
            assert_eq!(json["type"], "0x40");
            assert_eq!(json["hash"], vector["hash"]);
            assert_eq!(
                json["maxFeePerGas"],
                serde_json::to_value(tx.max_fee_per_gas).unwrap()
            );
            assert_eq!(json.get("accessList").is_some(), tx.access_list.is_some());
        }
    }
}
