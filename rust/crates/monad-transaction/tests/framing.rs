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

use std::fmt::Debug;

use alloy_consensus::{
    Receipt, Signed, TxEip1559, TxEip2930, TxEip4844, TxEip4844Variant, TxEip7702, TxLegacy,
};
use alloy_eips::{Decodable2718, Encodable2718};
use alloy_primitives::{Signature, U256};
use alloy_rlp::{Decodable, Encodable, Header};
use monad_transaction::{ReceiptEnvelope, TxEnvelope, TxType};

fn frame(list: bool, length: usize, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    Header {
        list,
        payload_length: length,
    }
    .encode(&mut out);
    out.extend_from_slice(payload);
    out
}

fn transactions() -> Vec<TxEnvelope> {
    let signature = Signature::new(U256::from(1), U256::from(1), false);
    let mut txs = vec![
        Signed::new_unhashed(TxLegacy::default(), signature).into(),
        Signed::new_unhashed(TxEip2930::default(), signature).into(),
        Signed::new_unhashed(TxEip1559::default(), signature).into(),
        Signed::new_unhashed(TxEip4844Variant::from(TxEip4844::default()), signature).into(),
        Signed::new_unhashed(TxEip7702::default(), signature).into(),
    ];
    let fixture: serde_json::Value = serde_json::from_str(include_str!(
        "../../../../category/execution/ethereum/core/test/monad_type40_vectors.json"
    ))
    .unwrap();
    for vector in fixture["vectors"].as_array().unwrap() {
        let raw = hex::decode(
            vector["canonical"]
                .as_str()
                .unwrap()
                .trim_start_matches("0x"),
        )
        .unwrap();
        txs.push(TxEnvelope::decode_2718_exact(&raw).unwrap());
    }
    txs
}

fn receipts() -> Vec<ReceiptEnvelope> {
    [
        TxType::Legacy,
        TxType::Eip2930,
        TxType::Eip1559,
        TxType::Eip4844,
        TxType::Eip7702,
        TxType::Monad,
    ]
    .into_iter()
    .map(|ty| ReceiptEnvelope::from_typed(ty, Receipt::default().with_bloom()))
    .collect()
}

fn assert_streamable<
    T: Encodable2718 + Decodable2718 + Encodable + Decodable + Debug + PartialEq,
>(
    values: Vec<T>,
) {
    let stream = values
        .iter()
        .flat_map(alloy_rlp::encode)
        .collect::<Vec<_>>();
    let mut remaining = stream.as_slice();
    for value in &values {
        let before = remaining;
        assert_eq!(T::network_decode(&mut remaining).unwrap(), *value);
        let consumed = &before[..before.len() - remaining.len()];
        assert_eq!(alloy_rlp::encode(value), consumed);
        assert_eq!(alloy_rlp::decode_exact::<T>(consumed).unwrap(), *value);
        // The network wrapper is not part of a typed envelope's trie commitment.
        assert_eq!(T::decode_2718_exact(&value.encoded_2718()).unwrap(), *value);
    }
    assert!(remaining.is_empty());
    let list = frame(true, stream.len(), &stream);
    assert_eq!(alloy_rlp::decode_exact::<Vec<T>>(list).unwrap(), values);
}

fn assert_rejected<T: Decodable2718 + Decodable + Debug>(bytes: &[u8]) {
    assert!(T::network_decode(&mut &bytes[..]).is_err(), "{bytes:02x?}");
    assert!(alloy_rlp::decode_exact::<T>(bytes).is_err());
    if !bytes.is_empty() {
        let list = frame(true, bytes.len(), bytes);
        assert!(alloy_rlp::decode_exact::<Vec<T>>(list).is_err());
    }
}

fn assert_strict<T: Encodable2718 + Decodable2718 + Decodable + Debug>(values: Vec<T>) {
    for value in values {
        let raw = value.encoded_2718();
        if value.type_flag().is_none() {
            // Legacy is a list, never a wrapped list or a type-0 typed envelope.
            assert_rejected::<T>(&alloy_rlp::encode(raw.as_slice()));
            assert_rejected::<T>(&alloy_rlp::encode([vec![0], raw].concat().as_slice()));
            continue;
        }
        assert_rejected::<T>(&raw);
        for length in 0..=raw.len() + 1 {
            if length != raw.len() {
                // A decoder must not steal bytes from the next RLP item.
                assert_rejected::<T>(&frame(false, length, &raw));
            }
        }
        let with_suffix = [raw.clone(), vec![0x80]].concat();
        assert_rejected::<T>(&frame(false, with_suffix.len(), &with_suffix));
        let nested = alloy_rlp::encode(raw.as_slice());
        assert_rejected::<T>(&alloy_rlp::encode(nested.as_slice()));
        for type_byte in [0, 0x7f, 0x80, 0xc0] {
            let mut unknown = raw.clone();
            unknown[0] = type_byte;
            assert_rejected::<T>(&alloy_rlp::encode(unknown.as_slice()));
        }
    }
    for empty in [vec![], vec![0x80], vec![0xc0], vec![0x40]] {
        assert_rejected::<T>(&empty);
    }
}

#[test]
fn mixed_transaction_network_stream_preserves_canonical_bytes() {
    assert_streamable(transactions());
}

#[test]
fn mixed_receipt_network_stream_preserves_canonical_bytes() {
    assert_streamable(receipts());
}

#[test]
fn transaction_network_items_require_exact_rlp_framing() {
    assert_strict(transactions());
}

#[test]
fn receipt_network_items_require_exact_rlp_framing() {
    assert_strict(receipts());
}
