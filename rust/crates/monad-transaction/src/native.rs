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

use alloy_consensus::{transaction::RlpEcdsaEncodableTx, Signed};
use alloy_eips::{eip2930::AccessList, Typed2718};
use alloy_primitives::{keccak256, Bytes, Signature, TxKind, B256, U256};
use alloy_rlp::{BufMut, Decodable, Encodable, Error, Header};
use serde::{Deserialize, Serialize};

use crate::MONAD_TX_TYPE;

/// The baseline cleartext, single-call, sender-paid universal transaction profile.
/// An absent access-list feature and an explicitly empty feature have different hashes.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TxMonad {
    pub chain_id: U256,
    #[serde(with = "quantity")]
    pub nonce: u64,
    #[serde(rename = "gas", with = "quantity")]
    pub gas_limit: u64,
    pub max_priority_fee_per_gas: U256,
    pub max_fee_per_gas: U256,
    pub to: TxKind,
    pub value: U256,
    pub input: Bytes,
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
    fn fields(&self, signature: Option<&Signature>) -> Vec<u8> {
        let mut features = Vec::new();
        feature(1, alloy_rlp::encode(self.nonce), &mut features);
        feature(2, alloy_rlp::encode(self.gas_limit), &mut features);
        let mut call = Vec::new();
        feature(1, alloy_rlp::encode(self.to), &mut call);
        feature(2, alloy_rlp::encode(self.value), &mut call);
        feature(3, alloy_rlp::encode(&self.input), &mut call);
        feature(3, list(&call), &mut features);
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
        let mut fields = alloy_rlp::encode(self.chain_id);
        fields.extend_from_slice(&list(&features));
        fields
    }

    pub fn encoded_for_signing(&self) -> Vec<u8> {
        let mut out = vec![MONAD_TX_TYPE];
        out.extend_from_slice(&list(&self.fields(None)));
        out
    }

    pub fn signature_hash(&self) -> B256 {
        keccak256(self.encoded_for_signing())
    }

    pub fn into_signed(self, signature: Signature) -> Signed<Self> {
        Signed::new_unhashed(self, signature)
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
        let chain_id = U256::decode(&mut body)?;
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
        let mut present = 0u8;
        while !features.is_empty() {
            let (key, mut value) = entry(&mut features, &mut previous)?;
            match key {
                1 => tx.nonce = u64::decode(&mut value)?,
                2 => tx.gas_limit = u64::decode(&mut value)?,
                3 => {
                    let mut call = Header::decode_bytes(&mut value, true)?;
                    let mut call_previous = 0;
                    for expected in 1..=3 {
                        let (key, mut field) = entry(&mut call, &mut call_previous)?;
                        if key != expected {
                            return Err(Error::Custom("missing call field"));
                        }
                        match key {
                            1 => tx.to = TxKind::decode(&mut field)?,
                            2 => tx.value = U256::decode(&mut field)?,
                            3 => tx.input = Bytes::decode(&mut field)?,
                            _ => unreachable!(),
                        }
                        finish(field)?;
                    }
                    finish(call)?;
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
                    tx.max_priority_fee_per_gas = U256::decode(&mut fees)?;
                    tx.max_fee_per_gas = U256::decode(&mut fees)?;
                    finish(fees)?;
                }
                _ => return Err(Error::Custom("unsupported Monad feature")),
            }
            present |= 1 << key;
            finish(value)?;
        }
        if present & 0xce != 0xce {
            return Err(Error::Custom("missing baseline feature"));
        }
        Ok(tx.into_signed(signature.ok_or(Error::Custom("missing sender signature"))?))
    }
}

impl Typed2718 for TxMonad {
    fn ty(&self) -> u8 {
        MONAD_TX_TYPE
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
