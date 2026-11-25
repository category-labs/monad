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

use alloy_consensus::{transaction::RlpEcdsaEncodableTx, SignableTransaction, Signed, Transaction};
use alloy_eips::{eip2930::AccessList, eip7702::SignedAuthorization, Typed2718};
use alloy_primitives::{Bytes, Signature, TxKind, B256, U256};
use alloy_rlp::{BufMut, Decodable, Encodable, Error, Header};
use serde::{Deserialize, Serialize};

use crate::{MONAD_CALLS_FEATURE, MONAD_TX_TYPE};

/// One cleartext entry in a native transaction, in signed execution order.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields, default)]
pub struct MonadCall {
    pub to: TxKind,
    pub value: U256,
    pub input: Bytes,
}

impl MonadCall {
    fn encode(&self) -> Vec<u8> {
        let mut fields = Vec::new();
        feature(1, alloy_rlp::encode(self.to), &mut fields);
        feature(2, alloy_rlp::encode(self.value), &mut fields);
        feature(3, alloy_rlp::encode(&self.input), &mut fields);
        list(&fields)
    }

    fn decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
        let mut fields = Header::decode_bytes(buf, true)?;
        let mut previous = 0;
        let mut call = Self::default();
        for expected in 1..=3 {
            let (key, mut field) = entry(&mut fields, &mut previous)?;
            if key != expected {
                return Err(Error::Custom("missing call field"));
            }
            match key {
                1 => call.to = TxKind::decode(&mut field)?,
                2 => call.value = U256::decode(&mut field)?,
                3 => call.input = Bytes::decode(&mut field)?,
                _ => unreachable!(),
            }
            finish(field)?;
        }
        finish(fields)?;
        Ok(call)
    }
}

/// Batches are nonempty and only their first entry may create a contract.
pub fn validate_batch(calls: &[MonadCall]) -> Result<(), &'static str> {
    if calls.is_empty() {
        return Err("calls must not be empty");
    }
    if calls.iter().skip(1).any(|call| call.to.is_create()) {
        return Err("only the first batch entry may create a contract");
    }
    Ok(())
}

/// The cleartext, sender-paid universal transaction profile.
/// An absent access-list feature and an explicitly empty feature have different hashes.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TxMonad {
    #[serde(with = "quantity")]
    pub chain_id: u64,
    #[serde(with = "quantity")]
    pub nonce: u64,
    #[serde(rename = "gas", with = "quantity")]
    pub gas_limit: u64,
    #[serde(with = "quantity_u128")]
    pub max_priority_fee_per_gas: u128,
    #[serde(with = "quantity_u128")]
    pub max_fee_per_gas: u128,
    pub to: TxKind,
    pub value: U256,
    pub input: Bytes,
    /// Complete signed batch. `None` selects CALL; `Some` selects CALLS, even
    /// for one entry. Batch transactions leave the scalar call fields empty.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub calls: Option<Vec<MonadCall>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub access_list: Option<AccessList>,
}

pub(crate) fn list(payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(payload.len() + 9);
    Header {
        list: true,
        payload_length: payload.len(),
    }
    .encode(&mut out);
    out.extend_from_slice(payload);
    out
}

fn feature(key: u8, value: impl AsRef<[u8]>, out: &mut Vec<u8>) {
    let mut entry = vec![key];
    entry.extend_from_slice(value.as_ref());
    out.extend_from_slice(&list(&entry));
}

pub(crate) fn finish(buf: &[u8]) -> alloy_rlp::Result<()> {
    if buf.is_empty() {
        Ok(())
    } else {
        Err(Error::UnexpectedLength)
    }
}

/// Return a feature's bounded payload. No nested decoder may consume its parent's suffix.
fn entry<'a>(buf: &mut &'a [u8], previous: &mut u8) -> alloy_rlp::Result<(u8, &'a [u8])> {
    let mut pair = Header::decode_bytes(buf, true)?;
    let key = Header::decode_bytes(&mut pair, false)?;
    if key.len() != 1 || key[0] <= *previous {
        return Err(Error::Custom(
            "feature keys must be unique ascending single bytes",
        ));
    }
    *previous = key[0];
    Ok((key[0], pair))
}

impl TxMonad {
    /// Validate the mutually exclusive CALL/CALLS payload and creation position.
    pub fn validate_calls(&self) -> Result<(), &'static str> {
        if let Some(calls) = &self.calls {
            if self.to != TxKind::Create || self.value != U256::ZERO || !self.input.is_empty() {
                return Err("calls cannot be combined with scalar call fields");
            }
            validate_batch(calls)?;
        }
        Ok(())
    }

    pub fn is_batch(&self) -> bool {
        self.calls.is_some()
    }

    /// The first signed entry, including a possible top-level creation.
    pub fn first_call(&self) -> MonadCall {
        self.calls
            .as_ref()
            .and_then(|calls| calls.first())
            .cloned()
            .unwrap_or_else(|| MonadCall {
                to: self.to,
                value: self.value,
                input: self.input.clone(),
            })
    }

    /// Conservative outflow for reserve forecasting, never an upfront batch
    /// affordability requirement: earlier entries may fund later ones.
    pub fn max_value_outflow(&self) -> U256 {
        self.calls.as_ref().map_or(self.value, |calls| {
            calls
                .iter()
                .fold(U256::ZERO, |sum, call| sum.saturating_add(call.value))
        })
    }

    fn fields(&self, signature: Option<&Signature>) -> Vec<u8> {
        let mut features = Vec::new();
        feature(1, alloy_rlp::encode(self.nonce), &mut features);
        feature(2, alloy_rlp::encode(self.gas_limit), &mut features);
        if self.calls.is_none() {
            feature(3, self.first_call().encode(), &mut features);
        }
        if let Some(access_list) = &self.access_list {
            feature(4, alloy_rlp::encode(access_list), &mut features);
        }
        let mut sig = Vec::new();
        if let Some(signature) = signature {
            signature.write_rlp_vrs(&mut sig, signature.v());
        }
        feature(6, list(&sig), &mut features);
        let mut fees = alloy_rlp::encode(self.max_priority_fee_per_gas);
        self.max_fee_per_gas.encode(&mut fees);
        feature(7, list(&fees), &mut features);
        if let Some(calls) = &self.calls {
            let mut encoded = Vec::new();
            for call in calls {
                encoded.extend_from_slice(&call.encode());
            }
            feature(MONAD_CALLS_FEATURE, list(&encoded), &mut features);
        }
        let mut fields = alloy_rlp::encode(self.chain_id);
        fields.extend_from_slice(&list(&features));
        fields
    }

    /// Encode the RPC-only wrapper. The auxiliary data is always an empty list.
    pub fn encode_submission(&self, signature: &Signature) -> Vec<u8> {
        let mut fields = self.fields(Some(signature));
        fields.push(0xc0);
        let mut out = vec![MONAD_TX_TYPE];
        out.extend_from_slice(&list(&fields));
        out
    }

    /// Decode one bounded canonical body, or the RPC-only three-field body.
    /// Unknown features are not executable in this profile and fail closed.
    pub(crate) fn decode_body(
        buf: &mut &[u8],
        submission: bool,
    ) -> alloy_rlp::Result<Signed<Self>> {
        let mut body = Header::decode_bytes(buf, true)?;
        let chain_id = u64::decode(&mut body)?;
        let mut features = Header::decode_bytes(&mut body, true)?;
        if submission {
            finish(Header::decode_bytes(&mut body, true)?)?;
        }
        finish(body)?;

        let mut tx = Self {
            chain_id,
            ..Self::default()
        };
        let mut signature = None;
        let mut previous = 0;
        let mut present = 0u16;
        while !features.is_empty() {
            let (key, mut value) = entry(&mut features, &mut previous)?;
            match key {
                1 => tx.nonce = u64::decode(&mut value)?,
                2 => tx.gas_limit = u64::decode(&mut value)?,
                3 => {
                    let call = MonadCall::decode(&mut value)?;
                    tx.to = call.to;
                    tx.value = call.value;
                    tx.input = call.input;
                }
                4 => tx.access_list = Some(AccessList::decode(&mut value)?),
                6 => {
                    let mut sig = Header::decode_bytes(&mut value, true)?;
                    let parity = u8::decode(&mut sig)?;
                    if parity > 1 {
                        return Err(Error::Custom("invalid signature parity"));
                    }
                    let r = U256::decode(&mut sig)?;
                    let s = U256::decode(&mut sig)?;
                    finish(sig)?;
                    signature = Some(Signature::new(r, s, parity != 0));
                }
                7 => {
                    let mut fees = Header::decode_bytes(&mut value, true)?;
                    tx.max_priority_fee_per_gas = u128::decode(&mut fees)?;
                    tx.max_fee_per_gas = u128::decode(&mut fees)?;
                    finish(fees)?;
                }
                MONAD_CALLS_FEATURE => {
                    let mut encoded = Header::decode_bytes(&mut value, true)?;
                    let mut calls = Vec::new();
                    while !encoded.is_empty() {
                        calls.push(MonadCall::decode(&mut encoded)?);
                    }
                    tx.calls = Some(calls);
                }
                _ => return Err(Error::Custom("unsupported Monad feature")),
            }
            present |= 1 << key;
            finish(value)?;
        }
        if present & 0xc6 != 0xc6 {
            return Err(Error::Custom("missing required feature"));
        }
        if (present & (1 << 3) != 0) == (present & (1 << MONAD_CALLS_FEATURE) != 0) {
            return Err(Error::Custom("exactly one of CALL and CALLS is required"));
        }
        tx.validate_calls().map_err(Error::Custom)?;
        Ok(tx.into_signed(signature.ok_or(Error::Custom("missing sender signature"))?))
    }
}

impl Typed2718 for TxMonad {
    fn ty(&self) -> u8 {
        MONAD_TX_TYPE
    }
}

impl Transaction for TxMonad {
    fn chain_id(&self) -> Option<u64> {
        Some(self.chain_id)
    }
    fn nonce(&self) -> u64 {
        self.nonce
    }
    fn gas_limit(&self) -> u64 {
        self.gas_limit
    }
    fn gas_price(&self) -> Option<u128> {
        None
    }
    fn max_fee_per_gas(&self) -> u128 {
        self.max_fee_per_gas
    }
    fn max_priority_fee_per_gas(&self) -> Option<u128> {
        Some(self.max_priority_fee_per_gas)
    }
    fn max_fee_per_blob_gas(&self) -> Option<u128> {
        None
    }
    fn priority_fee_or_price(&self) -> u128 {
        self.max_priority_fee_per_gas
    }
    fn effective_gas_price(&self, base_fee: Option<u64>) -> u128 {
        alloy_eips::eip1559::calc_effective_gas_price(
            self.max_fee_per_gas,
            self.max_priority_fee_per_gas,
            base_fee,
        )
    }
    fn is_dynamic_fee(&self) -> bool {
        true
    }
    fn kind(&self) -> TxKind {
        self.to
    }
    fn is_create(&self) -> bool {
        self.first_call().to.is_create()
    }
    fn value(&self) -> U256 {
        self.value
    }
    fn input(&self) -> &Bytes {
        &self.input
    }
    fn access_list(&self) -> Option<&AccessList> {
        self.access_list.as_ref()
    }
    fn blob_versioned_hashes(&self) -> Option<&[B256]> {
        None
    }
    fn authorization_list(&self) -> Option<&[SignedAuthorization]> {
        None
    }
}

impl SignableTransaction<Signature> for TxMonad {
    fn set_chain_id(&mut self, chain_id: u64) {
        self.chain_id = chain_id;
    }
    fn encode_for_signing(&self, out: &mut dyn BufMut) {
        out.put_u8(MONAD_TX_TYPE);
        out.put_slice(&list(&self.fields(None)));
    }
    fn payload_len_for_signature(&self) -> usize {
        1 + list(&self.fields(None)).len()
    }
}

impl RlpEcdsaEncodableTx for TxMonad {
    fn rlp_encoded_fields_length(&self) -> usize {
        self.fields(None).len()
    }
    fn rlp_encode_fields(&self, out: &mut dyn BufMut) {
        out.put_slice(&self.fields(None));
    }
    fn rlp_header_signed(&self, signature: &Signature) -> Header {
        Header {
            list: true,
            payload_length: self.fields(Some(signature)).len(),
        }
    }
    fn rlp_encode_signed(&self, signature: &Signature, out: &mut dyn BufMut) {
        out.put_slice(&list(&self.fields(Some(signature))));
    }
}

pub(crate) mod quantity {
    use alloy_primitives::U64;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(value: &u64, serializer: S) -> Result<S::Ok, S::Error> {
        U64::from(*value).serialize(serializer)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<u64, D::Error> {
        Ok(U64::deserialize(deserializer)?.to())
    }
}

mod quantity_u128 {
    use alloy_primitives::U128;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    pub fn serialize<S: Serializer>(value: &u128, serializer: S) -> Result<S::Ok, S::Error> {
        U128::from(*value).serialize(serializer)
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<u128, D::Error> {
        Ok(U128::deserialize(deserializer)?.to())
    }
}
