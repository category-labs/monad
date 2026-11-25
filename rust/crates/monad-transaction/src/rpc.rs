// Copyright (C) 2025-26 Category Labs, Inc.
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

//! RPC execution views. Native `calls` is the attempted prefix, not signed intent.
use alloy_consensus::{transaction::Recovered, Signed, Transaction as TransactionTrait};
use alloy_eips::{eip2930::AccessList, eip7702::SignedAuthorization, Typed2718};
use alloy_network_primitives::TransactionResponse;
use alloy_primitives::{Address, Bytes, TxKind, B256, U256};
pub use alloy_rpc_types::FeeHistory;
use alloy_rpc_types::{Header, Log};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{MonadCall, ReceiptEnvelope, TxEnvelope, TxMonad};

/// Origin of the native call information. RPC projections cannot be signed again.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum NativeExecution {
    #[default]
    Pending,
    Mined {
        calls_executed: u32,
    },
    /// Read from JSON-RPC; the full signed call list and feature presence are unknown.
    Projection,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transaction<T = TxEnvelope> {
    pub inner: Recovered<T>,
    pub block_hash: Option<B256>,
    pub block_number: Option<u64>,
    pub transaction_index: Option<u64>,
    pub effective_gas_price: Option<u128>,
    pub block_timestamp: Option<u64>,
    pub native_execution: NativeExecution,
}

impl<T: Default> Default for Transaction<T> {
    fn default() -> Self {
        alloy_rpc_types::Transaction::<T>::default().into()
    }
}

impl<T> From<alloy_rpc_types::Transaction<T>> for Transaction<T> {
    fn from(tx: alloy_rpc_types::Transaction<T>) -> Self {
        Self {
            inner: tx.inner,
            block_hash: tx.block_hash,
            block_number: tx.block_number,
            transaction_index: tx.transaction_index,
            effective_gas_price: tx.effective_gas_price,
            block_timestamp: tx.block_timestamp,
            native_execution: NativeExecution::Pending,
        }
    }
}

impl Transaction {
    /// Access canonical bytes only for locally constructed responses. For a response
    /// received over RPC, use `debug_getRawTransaction` and verify its hash instead.
    pub fn canonical_envelope(&self) -> Result<&TxEnvelope, &'static str> {
        if self.native_execution == NativeExecution::Projection {
            return Err("native RPC calls are an execution projection; fetch the raw transaction");
        }
        Ok(self.inner.inner())
    }

    pub fn try_into_canonical(self) -> Result<TxEnvelope, &'static str> {
        self.canonical_envelope()?;
        Ok(self.inner.into_inner())
    }

    pub fn calls_executed(&self) -> Option<u32> {
        match self.native_execution {
            NativeExecution::Mined { calls_executed } => Some(calls_executed),
            _ => None,
        }
    }

    fn scalar_call(&self) -> Option<(&TxKind, &U256, &Bytes)> {
        let tx = self.inner.as_monad()?.tx();
        let count = match self.native_execution {
            NativeExecution::Mined { calls_executed } => calls_executed as usize,
            NativeExecution::Projection => tx.calls.as_ref().map_or(0, Vec::len),
            NativeExecution::Pending if self.block_number.is_some() && !tx.is_batch() => 1,
            _ => 0,
        };
        if count != 1 {
            return None;
        }
        match &tx.calls {
            Some(calls) => calls
                .first()
                .map(|call| (&call.to, &call.value, &call.input)),
            None => Some((&tx.to, &tx.value, &tx.input)),
        }
    }

    /// Attempted entries include the failing entry and earlier rolled-back entries.
    pub fn calls(&self) -> Result<Option<Vec<MonadCall>>, &'static str> {
        let Some(signed) = self.inner.as_monad() else {
            return Ok(None);
        };
        let tx = signed.tx();
        if self.native_execution == NativeExecution::Projection {
            return Ok(Some(tx.calls.clone().unwrap_or_default()));
        }
        let count = match self.native_execution {
            NativeExecution::Mined { calls_executed } => calls_executed as usize,
            NativeExecution::Pending if self.block_number.is_none() => 0,
            NativeExecution::Pending if !tx.is_batch() => 1,
            _ => return Err("missing native batch execution metadata"),
        };
        let calls = tx.calls.clone().unwrap_or_else(|| vec![tx.first_call()]);
        if count > calls.len() || (self.block_number.is_some() && count == 0) {
            return Err("invalid native execution count");
        }
        Ok(Some(calls.into_iter().take(count).collect()))
    }
}

impl Serialize for Transaction {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let base = alloy_rpc_types::Transaction {
            inner: self.inner.clone(),
            block_hash: self.block_hash,
            block_number: self.block_number,
            transaction_index: self.transaction_index,
            effective_gas_price: self.effective_gas_price,
            block_timestamp: self.block_timestamp,
        };
        let mut value = serde_json::to_value(base).map_err(serde::ser::Error::custom)?;
        if let Some(calls) = self.calls().map_err(serde::ser::Error::custom)? {
            let scalar = if calls.len() == 1 {
                calls[0].clone()
            } else {
                MonadCall::default()
            };
            value["to"] = serde_json::to_value(scalar.to).map_err(serde::ser::Error::custom)?;
            value["value"] =
                serde_json::to_value(scalar.value).map_err(serde::ser::Error::custom)?;
            value["input"] =
                serde_json::to_value(scalar.input).map_err(serde::ser::Error::custom)?;
            value["calls"] = serde_json::to_value(calls).map_err(serde::ser::Error::custom)?;
            if value.get("accessList").is_none() {
                value["accessList"] = serde_json::json!([]);
            }
            value["authorizationList"] = serde_json::json!([]);
        }
        value.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Transaction {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let mut value = serde_json::Value::deserialize(deserializer)?;
        if value.get("type").and_then(|v| v.as_str()) != Some("0x40")
            || value.get("calls").is_none()
        {
            return serde_json::from_value::<alloy_rpc_types::Transaction<TxEnvelope>>(value)
                .map(Into::into)
                .map_err(serde::de::Error::custom);
        }
        let calls: Vec<MonadCall> =
            serde_json::from_value(value["calls"].clone()).map_err(serde::de::Error::custom)?;
        if !calls.is_empty() {
            crate::validate_batch(&calls).map_err(serde::de::Error::custom)?;
        }
        let quantity = |key: &str| -> Result<Option<u64>, D::Error> {
            value
                .get(key)
                .filter(|v| !v.is_null())
                .map(|v| {
                    serde_json::from_value::<alloy_primitives::U64>(v.clone())
                        .map(|n| n.to())
                        .map_err(serde::de::Error::custom)
                })
                .transpose()
        };
        let block_number = quantity("blockNumber")?;
        let transaction_index = quantity("transactionIndex")?;
        let block_timestamp = quantity("blockTimestamp")?;
        let block_hash =
            serde_json::from_value(value.get("blockHash").cloned().unwrap_or_default())
                .map_err(serde::de::Error::custom)?;
        let sender =
            serde_json::from_value(value["from"].clone()).map_err(serde::de::Error::custom)?;
        let effective_gas_price = value
            .get("gasPrice")
            .filter(|v| !v.is_null())
            .map(|v| serde_json::from_value::<alloy_primitives::U128>(v.clone()).map(|n| n.to()))
            .transpose()
            .map_err(serde::de::Error::custom)?;
        // These fields are projections. They cannot select CALL versus CALLS or
        // establish the optional feature presence committed by the signature.
        value["to"] = serde_json::Value::Null;
        value["value"] = serde_json::json!("0x0");
        value["input"] = serde_json::json!("0x");
        let signed: Signed<TxMonad> =
            serde_json::from_value(value).map_err(serde::de::Error::custom)?;
        Ok(Self {
            inner: Recovered::new_unchecked(TxEnvelope::Monad(signed), sender),
            block_hash,
            block_number,
            transaction_index,
            effective_gas_price,
            block_timestamp,
            native_execution: NativeExecution::Projection,
        })
    }
}

impl AsRef<TxEnvelope> for Transaction {
    /// Native envelopes from RPC are projections. Use `canonical_envelope` before encoding.
    fn as_ref(&self) -> &TxEnvelope {
        self.inner.inner()
    }
}
impl std::ops::Deref for Transaction {
    type Target = TxEnvelope;
    fn deref(&self) -> &Self::Target {
        self.inner.inner()
    }
}
impl Typed2718 for Transaction {
    fn ty(&self) -> u8 {
        self.inner.ty()
    }
}
impl TransactionResponse for Transaction {
    fn tx_hash(&self) -> B256 {
        *self.inner.tx_hash()
    }
    fn block_hash(&self) -> Option<B256> {
        self.block_hash
    }
    fn block_number(&self) -> Option<u64> {
        self.block_number
    }
    fn transaction_index(&self) -> Option<u64> {
        self.transaction_index
    }
    fn from(&self) -> Address {
        self.inner.signer()
    }
}
impl TransactionTrait for Transaction {
    fn chain_id(&self) -> Option<u64> {
        self.inner.chain_id()
    }

    fn nonce(&self) -> u64 {
        self.inner.nonce()
    }

    fn gas_limit(&self) -> u64 {
        self.inner.gas_limit()
    }

    fn gas_price(&self) -> Option<u128> {
        self.inner.gas_price()
    }

    fn max_fee_per_gas(&self) -> u128 {
        self.inner.max_fee_per_gas()
    }

    fn max_priority_fee_per_gas(&self) -> Option<u128> {
        self.inner.max_priority_fee_per_gas()
    }

    fn max_fee_per_blob_gas(&self) -> Option<u128> {
        self.inner.max_fee_per_blob_gas()
    }

    fn priority_fee_or_price(&self) -> u128 {
        self.inner.priority_fee_or_price()
    }

    fn effective_gas_price(&self, base_fee: Option<u64>) -> u128 {
        self.inner.effective_gas_price(base_fee)
    }

    fn is_dynamic_fee(&self) -> bool {
        self.inner.is_dynamic_fee()
    }

    fn kind(&self) -> TxKind {
        if self.inner.is_monad() {
            self.scalar_call().map_or(TxKind::Create, |call| *call.0)
        } else {
            self.inner.kind()
        }
    }

    fn is_create(&self) -> bool {
        self.kind().is_create()
    }

    fn value(&self) -> U256 {
        if self.inner.is_monad() {
            self.scalar_call().map_or(U256::ZERO, |call| *call.1)
        } else {
            self.inner.value()
        }
    }

    fn input(&self) -> &Bytes {
        static EMPTY: Bytes = Bytes::new();
        if self.inner.is_monad() {
            self.scalar_call().map_or(&EMPTY, |call| call.2)
        } else {
            self.inner.input()
        }
    }

    fn access_list(&self) -> Option<&AccessList> {
        self.inner.access_list()
    }

    fn blob_versioned_hashes(&self) -> Option<&[B256]> {
        self.inner.blob_versioned_hashes()
    }

    fn authorization_list(&self) -> Option<&[SignedAuthorization]> {
        self.inner.authorization_list()
    }
}

pub type TransactionReceipt<T = ReceiptEnvelope<Log>> = alloy_rpc_types::TransactionReceipt<T>;
pub type Block<T = Transaction, H = Header> = alloy_rpc_types::Block<T, H>;
