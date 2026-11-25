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

use alloy_network::{
    BuildResult, Ethereum, NetworkTransactionBuilder, NetworkWallet, TransactionBuilder,
    TransactionBuilderError,
};
use alloy_primitives::{Address, Bytes, TxKind, U256};
use alloy_rpc_types_eth::{AccessList, TransactionInput, TransactionInputKind, TransactionRequest};
use monad_transaction::{
    rpc, validate_batch, MonadCall, TxEnvelope, TxMonad, TxType, TypedTransaction, MONAD_TX_TYPE,
};
use serde::{Deserialize, Deserializer, Serialize};

use crate::MonadNetwork;

/// Ethereum request fields with explicit `0x40` selection and native validation.
/// `Default` retains Ethereum inference; [`Self::native`] opts into Monad encoding.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MonadTransactionRequest {
    pub inner: TransactionRequest,
    pub calls: Option<Vec<MonadCall>>,
    pub(crate) rpc_projection: bool,
}

impl Serialize for MonadTransactionRequest {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if self.rpc_projection {
            return Err(serde::ser::Error::custom(
                "native RPC calls are an execution projection; fetch the raw transaction",
            ));
        }
        #[derive(Serialize)]
        struct Request<'a> {
            #[serde(flatten)]
            inner: &'a TransactionRequest,
            #[serde(skip_serializing_if = "Option::is_none")]
            calls: &'a Option<Vec<MonadCall>>,
        }
        Request {
            inner: &self.inner,
            calls: &self.calls,
        }
        .serialize(serializer)
    }
}

impl MonadTransactionRequest {
    pub fn native() -> Self {
        Self {
            inner: TransactionRequest {
                transaction_type: Some(MONAD_TX_TYPE),
                ..Default::default()
            },
            calls: None,
            rpc_projection: false,
        }
    }

    pub fn is_native(&self) -> bool {
        self.inner.transaction_type == Some(MONAD_TX_TYPE)
    }

    pub fn with_type(mut self, ty: TxType) -> Self {
        self.inner.transaction_type = Some(ty.into());
        self
    }

    /// Select an atomic batch. Scalar call fields must be absent.
    pub fn with_calls(mut self, calls: Vec<MonadCall>) -> Self {
        self.inner.transaction_type = Some(MONAD_TX_TYPE);
        self.calls = Some(calls);
        self
    }

    /// Validate supplied fields without requiring the fields supplied by fillers.
    pub fn validate(&self) -> Result<(), &'static str> {
        if self.rpc_projection {
            return Err("native RPC calls are an execution projection; fetch the raw transaction");
        }
        if let Some(ty) = self.inner.transaction_type {
            TxType::try_from(ty).map_err(|_| "unsupported transaction type")?;
        }
        self.inner
            .input
            .unique_input()
            .map_err(|_| "input and data disagree")?;
        if let Some(calls) = &self.calls {
            if !self.is_native() {
                return Err("calls requires transaction type 0x40");
            }
            if self.inner.to.is_some()
                || self.inner.value.is_some()
                || self.inner.input.input.is_some()
                || self.inner.input.data.is_some()
            {
                return Err("calls cannot be combined with to, value, input or data");
            }
            validate_batch(calls)?;
        }
        if !self.is_native() {
            return Ok(());
        }
        let tx = &self.inner;
        if tx.gas_price.is_some() {
            return Err("native transactions require fee caps, not gasPrice");
        }
        if tx.authorization_list.is_some() {
            return Err("native authorization lists are not supported");
        }
        if tx.max_fee_per_blob_gas.is_some()
            || tx.blob_versioned_hashes.is_some()
            || tx.sidecar.is_some()
        {
            return Err("native blob transactions are not supported");
        }
        if let (Some(max), Some(priority)) = (tx.max_fee_per_gas, tx.max_priority_fee_per_gas) {
            if priority > max {
                return Err("maxPriorityFeePerGas exceeds maxFeePerGas");
            }
        }
        Ok(())
    }

    fn missing_native(&self) -> Vec<&'static str> {
        let tx = &self.inner;
        let mut missing = Vec::new();
        if tx.chain_id.is_none() {
            missing.push("chainId");
        }
        if tx.nonce.is_none() {
            missing.push("nonce");
        }
        if tx.gas.is_none() {
            missing.push("gas");
        }
        if tx.max_fee_per_gas.is_none() {
            missing.push("maxFeePerGas");
        }
        if tx.max_priority_fee_per_gas.is_none() {
            missing.push("maxPriorityFeePerGas");
        }
        missing
    }
}

impl<'de> Deserialize<'de> for MonadTransactionRequest {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct RequestVisitor;
        impl<'de> serde::de::Visitor<'de> for RequestVisitor {
            type Value = serde_json::Value;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a transaction object with unique fields")
            }

            fn visit_map<M: serde::de::MapAccess<'de>>(
                self,
                mut map: M,
            ) -> Result<Self::Value, M::Error> {
                let mut object = serde_json::Map::new();
                while let Some((key, value)) = map.next_entry::<String, serde_json::Value>()? {
                    if object.insert(key.clone(), value).is_some() {
                        return Err(serde::de::Error::custom(format!("duplicate field: {key}")));
                    }
                }
                Ok(serde_json::Value::Object(object))
            }
        }
        let value = deserializer.deserialize_map(RequestVisitor)?;
        let mut inner: TransactionRequest =
            serde_json::from_value(value.clone()).map_err(serde::de::Error::custom)?;
        let calls = value
            .get("calls")
            .map(|calls| serde_json::from_value::<Vec<MonadCall>>(calls.clone()))
            .transpose()
            .map_err(serde::de::Error::custom)?;
        if calls.is_some() && inner.transaction_type.is_none() {
            inner.transaction_type = Some(MONAD_TX_TYPE);
        }
        let request = Self {
            inner,
            calls,
            rpc_projection: false,
        };
        if request.is_native() {
            // Reject future feature requests instead of silently signing a different transaction.
            for key in value
                .as_object()
                .ok_or_else(|| serde::de::Error::custom("expected transaction object"))?
                .keys()
            {
                if !matches!(
                    key.as_str(),
                    "type"
                        | "chainId"
                        | "from"
                        | "to"
                        | "nonce"
                        | "gas"
                        | "value"
                        | "input"
                        | "data"
                        | "maxFeePerGas"
                        | "maxPriorityFeePerGas"
                        | "accessList"
                        | "calls"
                ) {
                    return Err(serde::de::Error::custom(format!(
                        "unsupported native field: {key}"
                    )));
                }
            }
        }
        request.validate().map_err(serde::de::Error::custom)?;
        Ok(request)
    }
}

impl From<TransactionRequest> for MonadTransactionRequest {
    fn from(inner: TransactionRequest) -> Self {
        Self {
            inner,
            calls: None,
            rpc_projection: false,
        }
    }
}
impl From<TxMonad> for MonadTransactionRequest {
    fn from(tx: TxMonad) -> Self {
        Self {
            inner: TransactionRequest {
                transaction_type: Some(MONAD_TX_TYPE),
                chain_id: Some(tx.chain_id),
                nonce: Some(tx.nonce),
                gas: Some(tx.gas_limit),
                max_fee_per_gas: Some(tx.max_fee_per_gas),
                max_priority_fee_per_gas: Some(tx.max_priority_fee_per_gas),
                to: tx.calls.is_none().then_some(tx.to),
                value: tx.calls.is_none().then_some(tx.value),
                input: if tx.calls.is_none() {
                    TransactionInput::new(tx.input)
                } else {
                    TransactionInput::default()
                },
                access_list: tx.access_list,
                ..Default::default()
            },
            calls: tx.calls,
            rpc_projection: false,
        }
    }
}
impl From<TypedTransaction> for MonadTransactionRequest {
    fn from(tx: TypedTransaction) -> Self {
        match tx {
            TypedTransaction::Ethereum(tx) => Self {
                inner: tx.into(),
                calls: None,
                rpc_projection: false,
            },
            TypedTransaction::Monad(tx) => tx.into(),
        }
    }
}
impl From<TxEnvelope> for MonadTransactionRequest {
    fn from(tx: TxEnvelope) -> Self {
        TypedTransaction::from(tx).into()
    }
}
impl From<rpc::Transaction> for MonadTransactionRequest {
    fn from(tx: rpc::Transaction) -> Self {
        let from = tx.inner.signer();
        let projection = tx.native_execution == rpc::NativeExecution::Projection;
        let mut request: Self = tx.inner.into_inner().into();
        request.rpc_projection = projection;
        request.inner.from = Some(from);
        request
    }
}

impl TransactionBuilder for MonadTransactionRequest {
    fn chain_id(&self) -> Option<u64> {
        self.inner.chain_id
    }
    fn set_chain_id(&mut self, id: u64) {
        self.inner.chain_id = Some(id);
    }
    fn nonce(&self) -> Option<u64> {
        self.inner.nonce
    }
    fn set_nonce(&mut self, nonce: u64) {
        self.inner.nonce = Some(nonce);
    }
    fn take_nonce(&mut self) -> Option<u64> {
        self.inner.nonce.take()
    }
    fn input(&self) -> Option<&Bytes> {
        self.inner.input.input()
    }
    fn set_input<T: Into<Bytes>>(&mut self, input: T) {
        self.inner.input = TransactionInput::new(input.into());
    }
    fn set_input_kind<T: Into<Bytes>>(&mut self, input: T, kind: TransactionInputKind) {
        self.inner.input = match kind {
            TransactionInputKind::Input => TransactionInput::new(input.into()),
            TransactionInputKind::Data => TransactionInput {
                input: None,
                data: Some(input.into()),
            },
            TransactionInputKind::Both => TransactionInput::both(input.into()),
        };
    }
    fn from(&self) -> Option<Address> {
        self.inner.from
    }
    fn set_from(&mut self, from: Address) {
        self.inner.from = Some(from);
    }
    fn kind(&self) -> Option<TxKind> {
        self.inner.to
    }
    fn clear_kind(&mut self) {
        self.inner.to = None;
    }
    fn set_kind(&mut self, kind: TxKind) {
        self.inner.to = Some(kind);
    }
    fn value(&self) -> Option<U256> {
        self.inner.value
    }
    fn set_value(&mut self, value: U256) {
        self.inner.value = Some(value);
    }
    fn gas_price(&self) -> Option<u128> {
        self.inner.gas_price
    }
    fn set_gas_price(&mut self, price: u128) {
        self.inner.gas_price = Some(price);
    }
    fn max_fee_per_gas(&self) -> Option<u128> {
        self.inner.max_fee_per_gas
    }
    fn set_max_fee_per_gas(&mut self, fee: u128) {
        self.inner.max_fee_per_gas = Some(fee);
    }
    fn max_priority_fee_per_gas(&self) -> Option<u128> {
        self.inner.max_priority_fee_per_gas
    }
    fn set_max_priority_fee_per_gas(&mut self, fee: u128) {
        self.inner.max_priority_fee_per_gas = Some(fee);
    }
    fn gas_limit(&self) -> Option<u64> {
        self.inner.gas
    }
    fn set_gas_limit(&mut self, gas: u64) {
        self.inner.gas = Some(gas);
    }
    fn access_list(&self) -> Option<&AccessList> {
        self.inner.access_list.as_ref()
    }
    fn set_access_list(&mut self, list: AccessList) {
        self.inner.access_list = Some(list);
    }
}

impl NetworkTransactionBuilder<MonadNetwork> for MonadTransactionRequest {
    fn can_submit(&self) -> bool {
        !self.is_native()
            && self.validate().is_ok()
            && NetworkTransactionBuilder::<Ethereum>::can_submit(&self.inner)
    }
    fn can_build(&self) -> bool {
        self.output_tx_type_checked().is_some()
    }
    fn complete_type(&self, ty: TxType) -> Result<(), Vec<&'static str>> {
        self.validate().map_err(|error| vec![error])?;
        if ty == TxType::Monad {
            let missing = self.missing_native();
            if missing.is_empty() {
                Ok(())
            } else {
                Err(missing)
            }
        } else {
            NetworkTransactionBuilder::<Ethereum>::complete_type(
                &self.inner,
                alloy_consensus::TxType::try_from(u8::from(ty)).expect("Ethereum type"),
            )
        }
    }
    fn output_tx_type(&self) -> TxType {
        if self.is_native() {
            TxType::Monad
        } else {
            TxType::try_from(u8::from(
                NetworkTransactionBuilder::<Ethereum>::output_tx_type(&self.inner),
            ))
            .expect("Ethereum type")
        }
    }
    fn output_tx_type_checked(&self) -> Option<TxType> {
        self.validate().ok()?;
        if self.is_native() {
            self.missing_native().is_empty().then_some(TxType::Monad)
        } else {
            NetworkTransactionBuilder::<Ethereum>::output_tx_type_checked(&self.inner)
                .map(|ty| TxType::try_from(u8::from(ty)).expect("Ethereum type"))
        }
    }
    fn prep_for_submission(&mut self) {
        if !self.is_native() {
            NetworkTransactionBuilder::<Ethereum>::prep_for_submission(&mut self.inner);
        }
    }
    fn build_unsigned(self) -> BuildResult<TypedTransaction, MonadNetwork> {
        if let Err(error) = self.validate() {
            return Err(TransactionBuilderError::Custom(error.into()).into_unbuilt(self));
        }
        if self.is_native() {
            let missing = self.missing_native();
            if !missing.is_empty() {
                return Err(TransactionBuilderError::InvalidTransactionRequest(
                    TxType::Monad,
                    missing,
                )
                .into_unbuilt(self));
            }
            let tx = self.inner;
            Ok(TxMonad {
                chain_id: tx.chain_id.expect("checked"),
                nonce: tx.nonce.expect("checked"),
                gas_limit: tx.gas.expect("checked"),
                max_fee_per_gas: tx.max_fee_per_gas.expect("checked"),
                max_priority_fee_per_gas: tx.max_priority_fee_per_gas.expect("checked"),
                to: tx.to.unwrap_or(TxKind::Create),
                value: tx.value.unwrap_or_default(),
                input: tx.input.into_input().unwrap_or_default(),
                calls: self.calls,
                access_list: tx.access_list,
            }
            .into())
        } else {
            NetworkTransactionBuilder::<Ethereum>::build_unsigned(self.inner)
                .map(Into::into)
                .map_err(|error| {
                    TransactionBuilderError::Custom(error.error.to_string().into())
                        .into_unbuilt(error.request.into())
                })
        }
    }
    async fn build<W: NetworkWallet<MonadNetwork>>(
        self,
        wallet: &W,
    ) -> Result<TxEnvelope, TransactionBuilderError<MonadNetwork>> {
        Ok(wallet.sign_request(self).await?)
    }
}
