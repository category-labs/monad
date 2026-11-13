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

//! Standard RPC fields with full-width native fee quantities.
use alloy_consensus::transaction::Recovered;
use alloy_primitives::{Address, B256, U256};
use alloy_rpc_types::{Header, Log};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{native::quantity, ReceiptEnvelope, TxEnvelope};

pub type Block<T = Transaction, H = Header> = alloy_rpc_types::Block<T, H>;

#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FeeHistory {
    #[serde(flatten)]
    pub inner: alloy_rpc_types::FeeHistory,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reward: Option<Vec<Vec<U256>>>,
}

impl std::ops::Deref for FeeHistory {
    type Target = alloy_rpc_types::FeeHistory;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transaction<T = TxEnvelope> {
    pub inner: Recovered<T>,
    pub block_hash: Option<B256>,
    pub block_number: Option<u64>,
    pub transaction_index: Option<u64>,
    pub effective_gas_price: Option<U256>,
    pub block_timestamp: Option<u64>,
}

impl<T: Default> Default for Transaction<T> {
    fn default() -> Self {
        Self {
            inner: Recovered::new_unchecked(T::default(), Address::ZERO),
            block_hash: None,
            block_number: None,
            transaction_index: None,
            effective_gas_price: None,
            block_timestamp: None,
        }
    }
}
impl<T> std::ops::Deref for Transaction<T> {
    type Target = Recovered<T>;
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}
impl<T> Transaction<T> {
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
    pub fn into_recovered(self) -> Recovered<T> {
        self.inner
    }
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct TransactionFields {
    from: Address,
    #[serde(default)]
    block_hash: Option<B256>,
    #[serde(default, with = "quantity_opt")]
    block_number: Option<u64>,
    #[serde(default, with = "quantity_opt")]
    transaction_index: Option<u64>,
    #[serde(default, rename = "gasPrice", skip_serializing_if = "Option::is_none")]
    effective_gas_price: Option<U256>,
    #[serde(
        default,
        with = "quantity_opt",
        skip_serializing_if = "Option::is_none"
    )]
    block_timestamp: Option<u64>,
}
impl<T: Serialize> Serialize for Transaction<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let fields = TransactionFields {
            from: self.inner.signer(),
            block_hash: self.block_hash,
            block_number: self.block_number,
            transaction_index: self.transaction_index,
            effective_gas_price: self.effective_gas_price,
            block_timestamp: self.block_timestamp,
        };
        let mut value =
            serde_json::to_value(self.inner.inner()).map_err(serde::ser::Error::custom)?;
        let metadata = serde_json::to_value(fields).map_err(serde::ser::Error::custom)?;
        value
            .as_object_mut()
            .ok_or_else(|| serde::ser::Error::custom("transaction must be an object"))?
            .extend(metadata.as_object().expect("metadata object").clone());
        value.serialize(serializer)
    }
}
impl<'de, T: serde::de::DeserializeOwned> Deserialize<'de> for Transaction<T> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = serde_json::Value::deserialize(deserializer)?;
        let fields: TransactionFields =
            serde_json::from_value(value.clone()).map_err(serde::de::Error::custom)?;
        let tx = serde_json::from_value(value).map_err(serde::de::Error::custom)?;
        Ok(Self {
            inner: Recovered::new_unchecked(tx, fields.from),
            block_hash: fields.block_hash,
            block_number: fields.block_number,
            transaction_index: fields.transaction_index,
            effective_gas_price: fields.effective_gas_price,
            block_timestamp: fields.block_timestamp,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransactionReceipt<T = ReceiptEnvelope<Log>> {
    #[serde(flatten)]
    pub inner: T,
    pub transaction_hash: B256,
    #[serde(default, with = "quantity_opt")]
    pub transaction_index: Option<u64>,
    pub block_hash: Option<B256>,
    #[serde(default, with = "quantity_opt")]
    pub block_number: Option<u64>,
    #[serde(with = "quantity")]
    pub gas_used: u64,
    #[serde(
        default,
        alias = "gasPrice",
        deserialize_with = "deserialize_effective_gas_price"
    )]
    pub effective_gas_price: U256,
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        with = "quantity_opt"
    )]
    pub blob_gas_used: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub blob_gas_price: Option<U256>,
    pub from: Address,
    pub to: Option<Address>,
    pub contract_address: Option<Address>,
}

fn deserialize_effective_gas_price<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<U256, D::Error> {
    Ok(Option::<U256>::deserialize(deserializer)?.unwrap_or_default())
}

impl<T: alloy_consensus::TxReceipt> TransactionReceipt<T> {
    pub fn status(&self) -> bool {
        self.inner.status()
    }
    pub fn logs(&self) -> &[T::Log] {
        self.inner.logs()
    }
}

mod quantity_opt {
    use alloy_primitives::U64;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(value: &Option<u64>, serializer: S) -> Result<S::Ok, S::Error> {
        value.map(U64::from).serialize(serializer)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Option<u64>, D::Error> {
        Ok(Option::<U64>::deserialize(deserializer)?.map(|v| v.to()))
    }
}
