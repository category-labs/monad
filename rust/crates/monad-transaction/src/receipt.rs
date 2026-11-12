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

use alloy_consensus::{Eip658Value, Receipt, ReceiptWithBloom, TxReceipt};
use alloy_eips::{
    eip2718::{Decodable2718, Eip2718Error, Eip2718Result, Encodable2718, IsTyped2718},
    Typed2718,
};
use alloy_primitives::{Bloom, Log};
use alloy_rlp::{BufMut, Decodable, Encodable, Header};
use serde::{Deserialize, Serialize};

use crate::{
    native::{finish, list},
    TxType, MONAD_TX_TYPE,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ReceiptEnvelope<T = Log> {
    #[serde(rename = "0x0", alias = "0x00")]
    Legacy(ReceiptWithBloom<Receipt<T>>),
    #[serde(rename = "0x1", alias = "0x01")]
    Eip2930(ReceiptWithBloom<Receipt<T>>),
    #[serde(rename = "0x2", alias = "0x02")]
    Eip1559(ReceiptWithBloom<Receipt<T>>),
    #[serde(rename = "0x3", alias = "0x03")]
    Eip4844(ReceiptWithBloom<Receipt<T>>),
    #[serde(rename = "0x4", alias = "0x04")]
    Eip7702(ReceiptWithBloom<Receipt<T>>),
    #[serde(rename = "0x40")]
    Monad(ReceiptWithBloom<Receipt<T>>),
}

impl<T> ReceiptEnvelope<T> {
    pub fn from_typed(ty: TxType, receipt: impl Into<ReceiptWithBloom<Receipt<T>>>) -> Self {
        match ty {
            TxType::Legacy => Self::Legacy(receipt.into()),
            TxType::Eip2930 => Self::Eip2930(receipt.into()),
            TxType::Eip1559 => Self::Eip1559(receipt.into()),
            TxType::Eip4844 => Self::Eip4844(receipt.into()),
            TxType::Eip7702 => Self::Eip7702(receipt.into()),
            TxType::Monad => Self::Monad(receipt.into()),
        }
    }
    pub fn tx_type(&self) -> TxType {
        match self {
            Self::Legacy(_) => TxType::Legacy,
            Self::Eip2930(_) => TxType::Eip2930,
            Self::Eip1559(_) => TxType::Eip1559,
            Self::Eip4844(_) => TxType::Eip4844,
            Self::Eip7702(_) => TxType::Eip7702,
            Self::Monad(_) => TxType::Monad,
        }
    }
    fn receipt(&self) -> &ReceiptWithBloom<Receipt<T>> {
        match self {
            Self::Legacy(r)
            | Self::Eip2930(r)
            | Self::Eip1559(r)
            | Self::Eip4844(r)
            | Self::Eip7702(r)
            | Self::Monad(r) => r,
        }
    }
    pub fn as_receipt_with_bloom(&self) -> Option<&ReceiptWithBloom<Receipt<T>>> {
        Some(self.receipt())
    }
    pub fn as_receipt(&self) -> Option<&Receipt<T>> {
        Some(&self.receipt().receipt)
    }
    pub fn into_receipt(self) -> Receipt<T> {
        match self {
            Self::Legacy(r)
            | Self::Eip2930(r)
            | Self::Eip1559(r)
            | Self::Eip4844(r)
            | Self::Eip7702(r)
            | Self::Monad(r) => r.receipt,
        }
    }
    pub fn status(&self) -> bool {
        self.receipt().receipt.status.coerce_status()
    }
    pub fn is_success(&self) -> bool {
        self.status()
    }
    pub fn cumulative_gas_used(&self) -> u64 {
        self.receipt().receipt.cumulative_gas_used
    }
    pub fn logs(&self) -> &[T] {
        &self.receipt().receipt.logs
    }
    pub fn logs_bloom(&self) -> &Bloom {
        &self.receipt().logs_bloom
    }
    pub fn into_primitives_receipt(self) -> ReceiptEnvelope<Log>
    where
        T: Into<Log>,
    {
        self.map_logs(Into::into)
    }
    pub fn map_logs<U>(self, f: impl FnMut(T) -> U) -> ReceiptEnvelope<U> {
        match self {
            Self::Legacy(r) => ReceiptEnvelope::Legacy(r.map_logs(f)),
            Self::Eip2930(r) => ReceiptEnvelope::Eip2930(r.map_logs(f)),
            Self::Eip1559(r) => ReceiptEnvelope::Eip1559(r.map_logs(f)),
            Self::Eip4844(r) => ReceiptEnvelope::Eip4844(r.map_logs(f)),
            Self::Eip7702(r) => ReceiptEnvelope::Eip7702(r.map_logs(f)),
            Self::Monad(r) => ReceiptEnvelope::Monad(r.map_logs(f)),
        }
    }
}

impl<T: Clone + std::fmt::Debug + PartialEq + Eq + Send + Sync> TxReceipt for ReceiptEnvelope<T> {
    type Log = T;
    fn status_or_post_state(&self) -> Eip658Value {
        self.receipt().receipt.status
    }
    fn status(&self) -> bool {
        self.status()
    }
    fn bloom(&self) -> Bloom {
        *self.logs_bloom()
    }
    fn bloom_cheap(&self) -> Option<Bloom> {
        Some(self.bloom())
    }
    fn cumulative_gas_used(&self) -> u64 {
        self.cumulative_gas_used()
    }
    fn logs(&self) -> &[T] {
        self.logs()
    }
    fn into_logs(self) -> Vec<T> {
        self.into_receipt().logs
    }
}
impl<T> Typed2718 for ReceiptEnvelope<T> {
    fn ty(&self) -> u8 {
        self.tx_type() as u8
    }
}
impl IsTyped2718 for ReceiptEnvelope {
    fn is_type(type_id: u8) -> bool {
        matches!(type_id, 0..=4 | MONAD_TX_TYPE)
    }
}

impl Encodable2718 for ReceiptEnvelope {
    fn encode_2718_len(&self) -> usize {
        if self.ty() == MONAD_TX_TYPE {
            let r = self.receipt();
            let n = r.receipt.status.length()
                + r.receipt.cumulative_gas_used.length()
                + r.logs_bloom.length()
                + r.receipt.logs.length()
                + 1;
            1 + Header {
                list: true,
                payload_length: n,
            }
            .length_with_payload()
        } else {
            self.receipt().length() + usize::from(self.ty() != 0)
        }
    }
    fn encode_2718(&self, out: &mut dyn BufMut) {
        if self.ty() != 0 {
            out.put_u8(self.ty());
        }
        if self.ty() == MONAD_TX_TYPE {
            let r = self.receipt();
            let mut fields = alloy_rlp::encode(r.receipt.status);
            r.receipt.cumulative_gas_used.encode(&mut fields);
            r.logs_bloom.encode(&mut fields);
            r.receipt.logs.encode(&mut fields);
            fields.push(0xc0);
            out.put_slice(&list(&fields));
        } else {
            self.receipt().encode(out);
        }
    }
}
impl Decodable2718 for ReceiptEnvelope {
    fn typed_decode(ty: u8, buf: &mut &[u8]) -> Eip2718Result<Self> {
        if ty == MONAD_TX_TYPE {
            let mut payload = Header::decode_bytes(buf, true)?;
            let status = bool::decode(&mut payload)?;
            let cumulative_gas_used = u64::decode(&mut payload)?;
            let logs_bloom = Bloom::decode(&mut payload)?;
            let logs = Vec::<Log>::decode(&mut payload)?;
            finish(Header::decode_bytes(&mut payload, true)?)?;
            finish(payload)?;
            return Ok(Self::Monad(ReceiptWithBloom {
                receipt: Receipt {
                    status: status.into(),
                    cumulative_gas_used,
                    logs,
                },
                logs_bloom,
            }));
        }
        let receipt = ReceiptWithBloom::<Receipt>::decode(buf)?;
        match ty {
            1 => Ok(Self::Eip2930(receipt)),
            2 => Ok(Self::Eip1559(receipt)),
            3 => Ok(Self::Eip4844(receipt)),
            4 => Ok(Self::Eip7702(receipt)),
            _ => Err(Eip2718Error::UnexpectedType(ty)),
        }
    }
    fn fallback_decode(buf: &mut &[u8]) -> Eip2718Result<Self> {
        Ok(Self::Legacy(ReceiptWithBloom::<Receipt>::decode(buf)?))
    }
    fn network_decode(buf: &mut &[u8]) -> Eip2718Result<Self> {
        crate::framing::network_decode(buf)
    }
}
impl Encodable for ReceiptEnvelope {
    fn encode(&self, out: &mut dyn BufMut) {
        self.network_encode(out);
    }
    fn length(&self) -> usize {
        self.network_len()
    }
}
impl Decodable for ReceiptEnvelope {
    fn decode(buf: &mut &[u8]) -> alloy_rlp::Result<Self> {
        Self::network_decode(buf).map_err(Into::into)
    }
}
