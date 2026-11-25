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

use alloy_primitives::{Address, Bloom, B256};
use monad_transaction::rpc::TransactionReceipt;
use serde_json::{json, Value};

fn receipt(transaction_type: u8) -> Value {
    json!({
        "type": format!("{transaction_type:#x}"),
        "status": "0x1",
        "cumulativeGasUsed": "0x5208",
        "logsBloom": Bloom::ZERO,
        "logs": [],
        "transactionHash": B256::repeat_byte(1),
        "gasUsed": "0x5208",
        "from": Address::repeat_byte(2),
    })
}

#[test]
fn receipt_price_defaults_only_missing_or_null_to_zero() {
    for transaction_type in [0, 1, 2, 3, 4, 0x40] {
        for field in [None, Some("effectiveGasPrice"), Some("gasPrice")] {
            let mut value = receipt(transaction_type);
            if let Some(field) = field {
                value[field] = Value::Null;
            }
            let decoded: TransactionReceipt = serde_json::from_value(value).unwrap();
            assert_eq!(decoded.effective_gas_price, 0);
            let encoded = serde_json::to_value(decoded).unwrap();
            assert_eq!(encoded["effectiveGasPrice"], "0x0");
            assert!(encoded.get("gasPrice").is_none());
        }
    }
}

#[test]
fn receipt_price_alias_and_canonical_field_preserve_uint128() {
    for transaction_type in [0, 1, 2, 3, 4, 0x40] {
        for field in ["effectiveGasPrice", "gasPrice"] {
            for price in [0, 1, u128::MAX] {
                let mut value = receipt(transaction_type);
                value[field] = json!(format!("{price:#x}"));
                let decoded: TransactionReceipt = serde_json::from_value(value).unwrap();
                assert_eq!(decoded.effective_gas_price, price);
                let encoded = serde_json::to_value(decoded).unwrap();
                assert_eq!(encoded["effectiveGasPrice"], format!("{price:#x}"));
                assert!(encoded.get("gasPrice").is_none());
                let roundtrip: TransactionReceipt = serde_json::from_value(encoded).unwrap();
                assert_eq!(roundtrip.effective_gas_price, price);
            }
        }
    }
}

#[test]
fn receipt_price_rejects_invalid_quantities_and_duplicate_aliases() {
    for transaction_type in [0, 1, 2, 3, 4, 0x40] {
        for field in ["effectiveGasPrice", "gasPrice"] {
            for invalid in [
                json!(false),
                json!([]),
                json!({}),
                json!("garbage"),
                json!(-1),
                json!("-0x1"),
                json!(format!("0x1{}", "0".repeat(32))),
                json!(format!("0x1{}", "0".repeat(64))),
            ] {
                let mut value = receipt(transaction_type);
                value[field] = invalid;
                assert!(
                    serde_json::from_value::<TransactionReceipt>(value.clone()).is_err(),
                    "{value}"
                );
            }
        }
        for price in [Value::Null, json!("0x1")] {
            let mut value = receipt(transaction_type);
            value["effectiveGasPrice"] = price.clone();
            value["gasPrice"] = price;
            assert!(serde_json::from_value::<TransactionReceipt>(value).is_err());
        }
    }
}

#[test]
fn batch_rpc_projects_attempts_without_losing_local_canonical_intent() {
    use alloy_consensus::{transaction::Recovered, SignableTransaction};
    use alloy_eips::Encodable2718;
    use alloy_primitives::{Bytes, Signature, TxKind, U256};
    use monad_transaction::{rpc, MonadCall, TxEnvelope, TxMonad};
    let calls = (1..=3)
        .map(|i| MonadCall {
            to: TxKind::Call(Address::repeat_byte(i)),
            value: U256::from(i),
            input: Bytes::from(vec![i]),
        })
        .collect::<Vec<_>>();
    let envelope: TxEnvelope = TxMonad {
        chain_id: 143,
        gas_limit: 100_000,
        calls: Some(calls.clone()),
        ..Default::default()
    }
    .into_signed(Signature::new(U256::ONE, U256::ONE, false))
    .into();
    let mut response = rpc::Transaction {
        inner: Recovered::new_unchecked(envelope.clone(), Address::ZERO),
        ..Default::default()
    };
    for count in 0..=3 {
        response.block_number = (count > 0).then_some(1);
        response.native_execution = if count == 0 {
            rpc::NativeExecution::Pending
        } else {
            rpc::NativeExecution::Mined {
                calls_executed: count,
            }
        };
        let json = serde_json::to_value(&response).unwrap();
        assert_eq!(
            json["calls"],
            serde_json::to_value(&calls[..count as usize]).unwrap()
        );
        assert_eq!(
            json["to"],
            if count == 1 {
                json!(calls[0].to)
            } else {
                Value::Null
            }
        );
        assert_eq!(
            json["value"],
            if count == 1 {
                json!("0x1")
            } else {
                json!("0x0")
            }
        );
        assert_eq!(
            json["input"],
            if count == 1 {
                json!("0x01")
            } else {
                json!("0x")
            }
        );
        assert_eq!(json["accessList"], json!([]));
        assert_eq!(
            response.canonical_envelope().unwrap().encoded_2718(),
            envelope.encoded_2718()
        );
        let projection: rpc::Transaction = serde_json::from_value(json.clone()).unwrap();
        assert_eq!(projection.inner.hash(), envelope.hash());
        assert!(projection.canonical_envelope().is_err());
        assert_eq!(serde_json::to_value(projection).unwrap(), json);
    }
    for count in [0, 4] {
        response.native_execution = rpc::NativeExecution::Mined {
            calls_executed: count,
        };
        assert!(serde_json::to_value(&response).is_err());
    }
}
