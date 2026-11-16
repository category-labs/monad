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

use alloy_consensus::{
    crypto::{secp256k1, RecoveryError},
    transaction::{Recovered, SignerRecoverable, TxHashRef},
    SignableTransaction, Signed, Transaction, TxEip1559, TxEip2930, TxEip4844Variant, TxEip7702,
    TxLegacy,
};
use alloy_eips::{
    eip2718::{Decodable2718, Eip2718Result, Encodable2718, IsTyped2718},
    eip2930::AccessList,
    eip7702::SignedAuthorization,
    Typed2718,
};
use alloy_primitives::{Address, Bytes, Signature, TxKind, B256, U256};
use alloy_rlp::{BufMut, Decodable, Encodable};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{native::finish, TxMonad, MONAD_TX_TYPE};

/// A canonical envelope shared by pool, block, execution bridge and RPC readers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TxEnvelope {
    Legacy(Signed<TxLegacy>),
    Eip2930(Signed<TxEip2930>),
    Eip1559(Signed<TxEip1559>),
    Eip4844(Signed<TxEip4844Variant>),
    Eip7702(Signed<TxEip7702>),
    Monad(Signed<TxMonad>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum TxType {
    Legacy = 0,
    Eip2930 = 1,
    Eip1559 = 2,
    Eip4844 = 3,
    Eip7702 = 4,
    Monad = 64,
}
impl Typed2718 for TxType {
    fn ty(&self) -> u8 {
        *self as u8
    }
}
impl std::fmt::Display for TxType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "0x{:x}", *self as u8)
    }
}

macro_rules! each {
    ($value:expr, $tx:ident => $expr:expr) => {
        match $value {
            TxEnvelope::Legacy($tx) => $expr,
            TxEnvelope::Eip2930($tx) => $expr,
            TxEnvelope::Eip1559($tx) => $expr,
            TxEnvelope::Eip4844($tx) => $expr,
            TxEnvelope::Eip7702($tx) => $expr,
            TxEnvelope::Monad($tx) => $expr,
        }
    };
}

impl TxEnvelope {
    pub const fn is_legacy(&self) -> bool {
        matches!(self, Self::Legacy(_))
    }
    pub const fn as_legacy(&self) -> Option<&Signed<TxLegacy>> {
        if let Self::Legacy(tx) = self {
            Some(tx)
        } else {
            None
        }
    }
    pub const fn is_eip2930(&self) -> bool {
        matches!(self, Self::Eip2930(_))
    }
    pub const fn as_eip2930(&self) -> Option<&Signed<TxEip2930>> {
        if let Self::Eip2930(tx) = self {
            Some(tx)
        } else {
            None
        }
    }
    pub const fn is_eip1559(&self) -> bool {
        matches!(self, Self::Eip1559(_))
    }
    pub const fn as_eip1559(&self) -> Option<&Signed<TxEip1559>> {
        if let Self::Eip1559(tx) = self {
            Some(tx)
        } else {
            None
        }
    }
    pub const fn is_eip4844(&self) -> bool {
        matches!(self, Self::Eip4844(_))
    }
    pub const fn as_eip4844(&self) -> Option<&Signed<TxEip4844Variant>> {
        if let Self::Eip4844(tx) = self {
            Some(tx)
        } else {
            None
        }
    }
    pub const fn is_eip7702(&self) -> bool {
        matches!(self, Self::Eip7702(_))
    }
    pub const fn as_eip7702(&self) -> Option<&Signed<TxEip7702>> {
        if let Self::Eip7702(tx) = self {
            Some(tx)
        } else {
            None
        }
    }
    pub const fn is_monad(&self) -> bool {
        matches!(self, Self::Monad(_))
    }
    pub const fn as_monad(&self) -> Option<&Signed<TxMonad>> {
        if let Self::Monad(tx) = self {
            Some(tx)
        } else {
            None
        }
    }
    pub const fn tx_type(&self) -> TxType {
        match self {
            Self::Legacy(_) => TxType::Legacy,
            Self::Eip2930(_) => TxType::Eip2930,
            Self::Eip1559(_) => TxType::Eip1559,
            Self::Eip4844(_) => TxType::Eip4844,
            Self::Eip7702(_) => TxType::Eip7702,
            Self::Monad(_) => TxType::Monad,
        }
    }
    pub fn signature_hash(&self) -> B256 {
        each!(self, tx => tx.signature_hash())
    }
    pub fn signature(&self) -> &Signature {
        each!(self, tx => tx.signature())
    }
    pub fn hash(&self) -> &B256 {
        each!(self, tx => tx.hash())
    }
    pub fn tx_hash(&self) -> &B256 {
        self.hash()
    }
    pub fn is_replay_protected(&self) -> bool {
        self.chain_id().is_some()
    }
    pub fn eip2718_encoded_length(&self) -> usize {
        self.encode_2718_len()
    }
    pub fn recover_signer(&self) -> Result<Address, RecoveryError> {
        SignerRecoverable::recover_signer(self)
    }
    pub fn recover_signer_unchecked(&self) -> Result<Address, RecoveryError> {
        SignerRecoverable::recover_signer_unchecked(self)
    }
    pub fn try_into_recovered(self) -> Result<Recovered<Self>, RecoveryError> {
        SignerRecoverable::try_into_recovered(self)
    }

    /// Only the RPC edge accepts the three-field native submission wrapper.
    pub fn decode_submission(bytes: &[u8]) -> Eip2718Result<Self> {
        if bytes.first() != Some(&MONAD_TX_TYPE) {
            return Self::decode_2718_exact(bytes);
        }
        let mut body = &bytes[1..];
        let tx = TxMonad::decode_body(&mut body, true)?;
        finish(body)?;
        Ok(Self::Monad(tx))
    }
}

impl Transaction for TxEnvelope {
    fn chain_id(&self) -> Option<u64> {
        each!(self, tx => tx.chain_id())
    }
    fn nonce(&self) -> u64 {
        each!(self, tx => tx.nonce())
    }
    fn gas_limit(&self) -> u64 {
        each!(self, tx => tx.gas_limit())
    }
    fn gas_price(&self) -> Option<u128> {
        each!(self, tx => tx.gas_price())
    }
    fn max_fee_per_gas(&self) -> u128 {
        each!(self, tx => tx.max_fee_per_gas())
    }
    fn max_priority_fee_per_gas(&self) -> Option<u128> {
        each!(self, tx => tx.max_priority_fee_per_gas())
    }
    fn max_fee_per_blob_gas(&self) -> Option<u128> {
        each!(self, tx => tx.max_fee_per_blob_gas())
    }
    fn priority_fee_or_price(&self) -> u128 {
        each!(self, tx => tx.priority_fee_or_price())
    }
    fn is_dynamic_fee(&self) -> bool {
        each!(self, tx => tx.is_dynamic_fee())
    }
    fn kind(&self) -> TxKind {
        each!(self, tx => tx.kind())
    }
    fn is_create(&self) -> bool {
        each!(self, tx => tx.is_create())
    }
    fn value(&self) -> U256 {
        each!(self, tx => tx.value())
    }
    fn input(&self) -> &Bytes {
        each!(self, tx => tx.input())
    }
    fn access_list(&self) -> Option<&AccessList> {
        each!(self, tx => tx.access_list())
    }
    fn blob_versioned_hashes(&self) -> Option<&[B256]> {
        each!(self, tx => tx.blob_versioned_hashes())
    }
    fn authorization_list(&self) -> Option<&[SignedAuthorization]> {
        each!(self, tx => tx.authorization_list())
    }
    fn effective_gas_price(&self, base_fee: Option<u64>) -> u128 {
        each!(self, tx => tx.effective_gas_price(base_fee))
    }
}

impl Typed2718 for TxEnvelope {
    fn ty(&self) -> u8 {
        self.tx_type() as u8
    }
}
impl IsTyped2718 for TxEnvelope {
    fn is_type(type_id: u8) -> bool {
        matches!(type_id, 0..=4 | MONAD_TX_TYPE)
    }
}
impl TxHashRef for TxEnvelope {
    fn tx_hash(&self) -> &B256 {
        self.hash()
    }
}
impl SignerRecoverable for TxEnvelope {
    fn recover_signer(&self) -> Result<Address, RecoveryError> {
        secp256k1::recover_signer(self.signature(), self.signature_hash())
    }
    fn recover_signer_unchecked(&self) -> Result<Address, RecoveryError> {
        secp256k1::recover_signer_unchecked(self.signature(), self.signature_hash())
    }
}
impl Encodable2718 for TxEnvelope {
    fn encode_2718_len(&self) -> usize {
        each!(self, tx => tx.encode_2718_len())
    }
    fn encode_2718(&self, out: &mut dyn BufMut) {
        each!(self, tx => tx.encode_2718(out));
    }
    fn trie_hash(&self) -> B256 {
        *self.hash()
    }
}
impl Decodable2718 for TxEnvelope {
    fn typed_decode(ty: u8, buf: &mut &[u8]) -> Eip2718Result<Self> {
        if ty == MONAD_TX_TYPE {
            return Ok(Self::Monad(TxMonad::decode_body(buf, false)?));
        }
        alloy_consensus::TxEnvelope::typed_decode(ty, buf).map(Into::into)
    }
    fn fallback_decode(buf: &mut &[u8]) -> Eip2718Result<Self> {
        alloy_consensus::TxEnvelope::fallback_decode(buf).map(Into::into)
    }
    fn network_decode(buf: &mut &[u8]) -> Eip2718Result<Self> {
        crate::framing::network_decode(buf)
    }
}
impl Encodable for TxEnvelope {
    fn encode(&self, out: &mut dyn BufMut) {
        self.network_encode(out);
    }
    fn length(&self) -> usize {
        self.network_len()
    }
}
impl Decodable for TxEnvelope {
    fn decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
        Self::network_decode(buf).map_err(Into::into)
    }
}
impl Default for TxEnvelope {
    fn default() -> Self {
        Self::Legacy(Signed::new_unhashed(
            TxLegacy::default(),
            Signature::new(U256::ZERO, U256::ZERO, false),
        ))
    }
}
impl From<alloy_consensus::TxEnvelope> for TxEnvelope {
    fn from(value: alloy_consensus::TxEnvelope) -> Self {
        match value {
            alloy_consensus::TxEnvelope::Legacy(tx) => Self::Legacy(tx),
            alloy_consensus::TxEnvelope::Eip2930(tx) => Self::Eip2930(tx),
            alloy_consensus::TxEnvelope::Eip1559(tx) => Self::Eip1559(tx),
            alloy_consensus::TxEnvelope::Eip4844(tx) => Self::Eip4844(tx),
            alloy_consensus::TxEnvelope::Eip7702(tx) => Self::Eip7702(tx),
        }
    }
}
impl From<Signed<TxLegacy>> for TxEnvelope {
    fn from(tx: Signed<TxLegacy>) -> Self {
        Self::Legacy(tx)
    }
}
impl From<Signed<TxEip2930>> for TxEnvelope {
    fn from(tx: Signed<TxEip2930>) -> Self {
        Self::Eip2930(tx)
    }
}
impl From<Signed<TxEip1559>> for TxEnvelope {
    fn from(tx: Signed<TxEip1559>) -> Self {
        Self::Eip1559(tx)
    }
}
impl From<Signed<TxEip4844Variant>> for TxEnvelope {
    fn from(tx: Signed<TxEip4844Variant>) -> Self {
        Self::Eip4844(tx)
    }
}
impl From<Signed<TxEip7702>> for TxEnvelope {
    fn from(tx: Signed<TxEip7702>) -> Self {
        Self::Eip7702(tx)
    }
}
impl From<Signed<TxMonad>> for TxEnvelope {
    fn from(tx: Signed<TxMonad>) -> Self {
        Self::Monad(tx)
    }
}

impl Serialize for TxEnvelope {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Monad(tx) => {
                #[derive(Serialize)]
                struct Native<'a> {
                    #[serde(rename = "type")]
                    ty: &'static str,
                    #[serde(flatten)]
                    tx: &'a Signed<TxMonad>,
                }
                Native { ty: "0x40", tx }.serialize(serializer)
            }
            Self::Legacy(tx) => {
                alloy_consensus::TxEnvelope::Legacy(tx.clone()).serialize(serializer)
            }
            Self::Eip2930(tx) => {
                alloy_consensus::TxEnvelope::Eip2930(tx.clone()).serialize(serializer)
            }
            Self::Eip1559(tx) => {
                alloy_consensus::TxEnvelope::Eip1559(tx.clone()).serialize(serializer)
            }
            Self::Eip4844(tx) => {
                alloy_consensus::TxEnvelope::Eip4844(tx.clone()).serialize(serializer)
            }
            Self::Eip7702(tx) => {
                alloy_consensus::TxEnvelope::Eip7702(tx.clone()).serialize(serializer)
            }
        }
    }
}
impl<'de> Deserialize<'de> for TxEnvelope {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = serde_json::Value::deserialize(deserializer)?;
        if value.get("type").and_then(|v| v.as_str()) == Some("0x40") {
            if let Some(price) = value.get("gasPrice").filter(|price| !price.is_null()) {
                serde_json::from_value::<alloy_primitives::U128>(price.clone())
                    .map_err(serde::de::Error::custom)?;
            }
            let signed: Signed<TxMonad> =
                serde_json::from_value(value).map_err(serde::de::Error::custom)?;
            let (tx, signature, claimed_hash) = signed.into_parts();
            let signed = tx.into_signed(signature);
            if *signed.hash() != claimed_hash {
                return Err(serde::de::Error::custom(
                    "incorrect native transaction hash",
                ));
            }
            Ok(Self::Monad(signed))
        } else {
            serde_json::from_value::<alloy_consensus::TxEnvelope>(value)
                .map(Into::into)
                .map_err(serde::de::Error::custom)
        }
    }
}
