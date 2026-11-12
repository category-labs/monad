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

use alloy_consensus::{transaction::Recovered, Receipt, ReceiptWithBloom, Signed, TxLegacy};
use alloy_eips::{Decodable2718, Encodable2718};
use alloy_primitives::{keccak256, Address, Bloom, Signature, B256, U256};
use alloy_rlp::{Decodable, Encodable, Header};
use monad_transaction::{rpc, ReceiptEnvelope, TxEnvelope};
use serde::Deserialize;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Vector {
    name: String,
    sender: Address,
    signing_payload: String,
    signing_hash: B256,
    canonical: String,
    hash: B256,
    submission: String,
}

fn vectors() -> Vec<Vector> {
    #[derive(Deserialize)]
    struct Fixture {
        vectors: Vec<Vector>,
    }
    serde_json::from_str::<Fixture>(include_str!(
        "../../../../category/execution/ethereum/core/test/monad_type40_vectors.json"
    ))
    .unwrap()
    .vectors
}
fn bytes(hex: &str) -> Vec<u8> {
    hex::decode(hex.strip_prefix("0x").unwrap()).unwrap()
}
fn list(data: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    Header {
        list: true,
        payload_length: data.len(),
    }
    .encode(&mut out);
    out.extend_from_slice(data);
    out
}
fn raw_items(mut input: &[u8]) -> Vec<Vec<u8>> {
    let mut items = Vec::new();
    while !input.is_empty() {
        let before = input;
        let header = Header::decode(&mut input).unwrap();
        input = &input[header.payload_length..];
        items.push(before[..before.len() - input.len()].to_vec());
    }
    items
}
fn change_features(raw: &[u8], change: impl FnOnce(&mut Vec<Vec<u8>>)) -> Vec<u8> {
    let mut body = &raw[1..];
    let body = Header::decode_bytes(&mut body, true).unwrap();
    let fields = raw_items(body);
    let mut encoded_features = fields[1].as_slice();
    let mut features = raw_items(Header::decode_bytes(&mut encoded_features, true).unwrap());
    change(&mut features);
    let fields = [fields[0].clone(), list(&features.concat())].concat();
    [vec![0x40], list(&fields)].concat()
}

#[test]
fn sdk_vectors_agree_on_bytes_hash_digest_sender_and_network_framing() {
    for v in vectors() {
        let raw = bytes(&v.canonical);
        let tx = TxEnvelope::decode_2718_exact(&raw).unwrap();
        assert_eq!(tx.encoded_2718(), raw, "{}", v.name);
        assert_eq!(*tx.hash(), v.hash, "{}", v.name);
        assert_eq!(tx.signature_hash(), v.signing_hash, "{}", v.name);
        assert_eq!(tx.recover_signer().unwrap(), v.sender, "{}", v.name);
        let native = tx.as_monad().unwrap();
        assert_eq!(native.tx().encoded_for_signing(), bytes(&v.signing_payload));
        assert_eq!(
            native.tx().encode_submission(native.signature()),
            bytes(&v.submission)
        );
        assert_eq!(
            TxEnvelope::decode_submission(&bytes(&v.submission)).unwrap(),
            tx
        );
        assert_ne!(keccak256(bytes(&v.submission)), v.hash);
        let network = alloy_rlp::encode(&tx);
        assert_eq!(TxEnvelope::decode(&mut network.as_slice()).unwrap(), tx);
        let json = serde_json::to_value(&tx).unwrap();
        assert_eq!(serde_json::from_value::<TxEnvelope>(json).unwrap(), tx);
    }
}

#[test]
fn commitment_boundaries_reject_wrong_framing_auxiliary_and_suffixes() {
    for v in vectors() {
        let canonical = bytes(&v.canonical);
        let submission = bytes(&v.submission);
        assert!(TxEnvelope::decode_submission(&canonical).is_err());
        assert!(TxEnvelope::decode_2718_exact(&submission).is_err());
        for len in 0..canonical.len() {
            assert!(TxEnvelope::decode_2718_exact(&canonical[..len]).is_err());
        }
        assert!(TxEnvelope::decode_2718_exact(&[canonical, vec![0x80]].concat()).is_err());
        let mut body = &submission[1..];
        let fields = raw_items(Header::decode_bytes(&mut body, true).unwrap());
        for aux in [vec![0x80], vec![0xc1, 0x80], vec![0xc0, 0xc0]] {
            let raw = [
                vec![0x40],
                list(&[fields[0].clone(), fields[1].clone(), aux].concat()),
            ]
            .concat();
            assert!(TxEnvelope::decode_submission(&raw).is_err());
        }
    }
}

#[test]
fn rejects_noncanonical_missing_and_unsupported_features() {
    let raw = bytes(&vectors()[1].canonical);
    let mutations: Vec<Box<dyn FnOnce(&mut Vec<Vec<u8>>)>> = vec![
        Box::new(|f| f.swap(0, 1)),
        Box::new(|f| f.insert(1, f[0].clone())),
        Box::new(|f| {
            f.remove(0);
        }),
        Box::new(|f| f.insert(3, vec![0xc2, 0x05, 0xc0])),
        Box::new(|f| f.push(vec![0xc2, 0x08, 0xc0])),
        Box::new(|f| f[0] = vec![0xc2, 0x01, 0x00]),
        Box::new(|f| f[0] = vec![0xc3, 0x01, 0x81, 0x01]),
        Box::new(|f| f[0] = vec![0xc4, 0x81, 0x01, 0x80, 0x80]),
        Box::new(|f| f[0] = [vec![0xcb, 0x01, 0x89], vec![0x01; 9]].concat()),
        // A child claims bytes beyond its feature's parent boundary.
        Box::new(|f| f[2] = vec![0xc3, 0x03, 0xf8, 0xff]),
        Box::new(|f| f[3] = vec![0xc2, 0x06, 0xc0]),
        Box::new(|f| f[3] = vec![0xc6, 0x06, 0xc3, 0x02, 0x01, 0x01, 0x80]),
    ];
    for mutate in mutations {
        assert!(TxEnvelope::decode_2718_exact(&change_features(&raw, mutate)).is_err());
    }
}

#[test]
fn absence_and_empty_access_list_have_distinct_commitments() {
    let vectors = vectors();
    let absent = TxEnvelope::decode_2718_exact(&bytes(&vectors[1].canonical)).unwrap();
    let empty = TxEnvelope::decode_2718_exact(&bytes(&vectors[2].canonical)).unwrap();
    assert!(absent.access_list().is_none());
    assert_eq!(empty.access_list().unwrap().len(), 0);
    assert_ne!(absent.signature_hash(), empty.signature_hash());
    assert_ne!(absent.hash(), empty.hash());
}

#[test]
fn low_s_is_a_validity_rule_and_never_a_decode_rewrite() {
    let tx = TxEnvelope::decode_2718_exact(&bytes(&vectors()[1].canonical)).unwrap();
    let signed = tx.as_monad().unwrap();
    let order = U256::from_str_radix(
        "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        16,
    )
    .unwrap();
    let sig = signed.signature();
    let high: TxEnvelope = signed
        .tx()
        .clone()
        .into_signed(Signature::new(sig.r(), order - sig.s(), !sig.v()))
        .into();
    let decoded = TxEnvelope::decode_2718_exact(&high.encoded_2718()).unwrap();
    assert_eq!(decoded, high);
    assert_ne!(decoded.hash(), tx.hash());
    assert!(decoded.recover_signer().is_err());
    for sig in [
        Signature::new(U256::ZERO, U256::ONE, false),
        Signature::new(order, U256::ONE, false),
        Signature::new(U256::ONE, U256::ZERO, false),
    ] {
        let bad: TxEnvelope = signed.tx().clone().into_signed(sig).into();
        assert!(bad.recover_signer().is_err());
    }
}

#[test]
fn receipt_requires_fifth_empty_extension_field() {
    let receipt = ReceiptWithBloom {
        receipt: Receipt {
            status: true.into(),
            cumulative_gas_used: 21000,
            logs: vec![],
        },
        logs_bloom: Bloom::ZERO,
    };
    let native = ReceiptEnvelope::Monad(receipt.clone());
    let mut fields = alloy_rlp::encode(true);
    21000u64.encode(&mut fields);
    Bloom::ZERO.encode(&mut fields);
    fields.extend_from_slice(&[0xc0, 0xc0]);
    let expected = [vec![0x40], list(&fields)].concat();
    assert_eq!(native.encoded_2718(), expected);
    assert_eq!(native.encode_2718_len(), expected.len());
    assert_eq!(
        ReceiptEnvelope::decode_2718_exact(&expected).unwrap(),
        native
    );
    let mut ethereum_as_native = ReceiptEnvelope::Eip1559(receipt).encoded_2718();
    ethereum_as_native[0] = 0x40;
    assert!(ReceiptEnvelope::decode_2718_exact(&ethereum_as_native).is_err());
    assert_ne!(keccak256(ethereum_as_native), keccak256(expected));
    fields.pop();
    fields.extend_from_slice(&[0xc1, 0x80]);
    assert!(ReceiptEnvelope::decode_2718_exact(&[vec![0x40], list(&fields)].concat()).is_err());
}

#[test]
fn rpc_roundtrip_retains_native_widths_and_ethereum_gas_price() {
    let native = TxEnvelope::decode_2718_exact(&bytes(&vectors()[5].canonical)).unwrap();
    let legacy = TxEnvelope::Legacy(Signed::new_unhashed(
        TxLegacy {
            gas_price: 2000000000,
            ..Default::default()
        },
        Signature::new(U256::ONE, U256::ONE, false),
    ));
    for tx in [native, legacy] {
        let rpc = rpc::Transaction {
            effective_gas_price: Some(tx.effective_gas_price(Some(1))),
            inner: Recovered::new_unchecked(tx.clone(), Address::ZERO),
            block_hash: Some(B256::ZERO),
            block_number: Some(1),
            transaction_index: Some(0),
            block_timestamp: Some(1),
        };
        let encoded = serde_json::to_value(&rpc).unwrap();
        assert_eq!(
            encoded["from"],
            serde_json::to_value(Address::ZERO).unwrap()
        );
        assert_eq!(
            encoded["gasPrice"],
            serde_json::to_value(rpc.effective_gas_price).unwrap()
        );
        assert_eq!(
            serde_json::from_value::<rpc::Transaction>(encoded).unwrap(),
            rpc
        );
    }
}

#[test]
fn native_and_ethereum_effective_fees_follow_the_same_rules() {
    use alloy_consensus::{SignableTransaction, Transaction, TxEip1559};
    let ethereum = TxEip1559 {
        max_fee_per_gas: 100,
        max_priority_fee_per_gas: 10,
        ..Default::default()
    };
    let native = monad_transaction::TxMonad {
        max_fee_per_gas: U256::from(100),
        max_priority_fee_per_gas: U256::from(10),
        ..Default::default()
    };
    let sig = Signature::new(U256::ONE, U256::ONE, false);
    let wrapped: TxEnvelope = ethereum.clone().into_signed(sig).into();
    let native: TxEnvelope = native.into_signed(sig).into();
    for base_fee in [None, Some(0), Some(50), Some(95), Some(100), Some(101)] {
        let expected = U256::from(ethereum.effective_gas_price(base_fee));
        assert_eq!(wrapped.effective_gas_price(base_fee), expected);
        assert_eq!(native.effective_gas_price(base_fee), expected);
    }
}

#[test]
fn fee_history_reward_preserves_full_width_quantities() {
    let history = rpc::FeeHistory {
        inner: alloy_rpc_types::FeeHistory {
            oldest_block: 1,
            base_fee_per_gas: vec![1, 2],
            gas_used_ratio: vec![0.5],
            ..Default::default()
        },
        reward: Some(vec![vec![U256::ONE << 200]]),
    };
    let json = serde_json::to_string(&history).unwrap();
    assert_eq!(json.matches("\"reward\"").count(), 1);
    assert_eq!(
        serde_json::from_str::<rpc::FeeHistory>(&json).unwrap(),
        history
    );
}

#[test]
fn trie_roots_commit_canonical_transactions_and_five_field_receipts() {
    fn single_leaf_root(value: &[u8]) -> B256 {
        // RLP(0) is 0x80; the leaf's even-length compact path is 0x20,0x80.
        let mut leaf = alloy_rlp::encode(alloy_primitives::Bytes::from_static(&[0x20, 0x80]));
        alloy_primitives::Bytes::copy_from_slice(value).encode(&mut leaf);
        keccak256(list(&leaf))
    }
    let vector = &vectors()[1];
    let canonical = bytes(&vector.canonical);
    let tx = TxEnvelope::decode_2718_exact(&canonical).unwrap();
    assert_eq!(
        alloy_consensus::proofs::calculate_transaction_root(&[tx]),
        single_leaf_root(&canonical)
    );
    assert_ne!(
        single_leaf_root(&canonical),
        single_leaf_root(&bytes(&vector.submission))
    );

    let receipt = ReceiptEnvelope::Monad(ReceiptWithBloom {
        receipt: Receipt {
            status: true.into(),
            cumulative_gas_used: 21000,
            logs: vec![],
        },
        logs_bloom: Bloom::ZERO,
    });
    assert_eq!(
        alloy_consensus::proofs::calculate_receipt_root(&[receipt.clone()]),
        single_leaf_root(&receipt.encoded_2718())
    );
}
