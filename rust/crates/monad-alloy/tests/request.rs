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

use alloy_consensus::{SignableTransaction, Signed, Transaction};
use alloy_eips::{Decodable2718, Encodable2718, Typed2718};
use alloy_network::{EthereumWallet, NetworkTransactionBuilder, TransactionBuilder};
use alloy_primitives::{Address, Bytes, Signature, TxKind, B256, U256};
use alloy_signer::SignerSync;
use alloy_signer_local::PrivateKeySigner;
use monad_alloy::{MonadTransactionRequest, TxEnvelope, TxMonad, TxType, TypedTransaction};
use serde_json::{json, Value};

fn signer() -> PrivateKeySigner {
    PrivateKeySigner::from_bytes(&B256::with_last_byte(1)).unwrap()
}

fn complete() -> MonadTransactionRequest {
    MonadTransactionRequest::native()
        .with_chain_id(20143)
        .with_nonce(0)
        .with_gas_limit(21_000)
        .with_max_fee_per_gas(50_000_000_000)
        .with_max_priority_fee_per_gas(2_000_000_000)
        .with_to(Address::with_last_byte(2))
}

#[tokio::test]
async fn wallet_signing_matches_independent_viem_vectors() {
    let fixture: Value =
        serde_json::from_str(include_str!("fixtures/monad_type40_vectors.json")).unwrap();
    let wallet = EthereumWallet::from(signer());
    for vector in fixture["vectors"].as_array().unwrap() {
        if matches!(vector["name"].as_str(), Some("wide-fees" | "wide-chain-id")) {
            continue;
        }
        let canonical: Bytes = serde_json::from_value(vector["canonical"].clone()).unwrap();
        let expected = TxEnvelope::decode_2718_exact(&canonical).unwrap();
        let request: MonadTransactionRequest = expected.clone().into();
        assert_eq!(request.inner.transaction_type, Some(0x40));
        let json = serde_json::to_value(&request).unwrap();
        let request: MonadTransactionRequest = serde_json::from_value(json).unwrap();
        let signed = request.build(&wallet).await.unwrap();
        assert_eq!(signed.encoded_2718(), canonical, "{}", vector["name"]);
        assert_eq!(signed.hash(), expected.hash());
        assert_eq!(signed.signature_hash(), expected.signature_hash());
        assert_eq!(signed.recover_signer().unwrap(), signer().address());
    }
}

#[test]
fn native_selection_is_explicit_and_survives_submission_preparation() {
    let native = complete();
    assert_eq!(native.output_tx_type(), TxType::Monad);
    let mut prepared = native.clone();
    prepared.prep_for_submission();
    assert_eq!(prepared, native);
    assert!(!native.can_submit());
    let mut ethereum = native;
    ethereum.inner.transaction_type = None;
    assert_eq!(ethereum.output_tx_type(), TxType::Eip1559);
    assert!(matches!(
        ethereum.build_unsigned().unwrap(),
        TypedTransaction::Ethereum(_)
    ));
}

#[test]
fn native_builder_requires_chain_id_and_fee_fields() {
    for field in [
        "chainId",
        "nonce",
        "gas",
        "maxFeePerGas",
        "maxPriorityFeePerGas",
    ] {
        let mut value = serde_json::to_value(complete()).unwrap();
        value.as_object_mut().unwrap().remove(field);
        let request: MonadTransactionRequest = serde_json::from_value(value).unwrap();
        assert!(!request.can_build(), "{field}");
        assert!(request.build_unsigned().is_err(), "{field}");
    }
}

#[test]
fn native_json_rejects_unsupported_fields_even_when_empty() {
    for (field, value) in [
        ("authorizationList", json!([])),
        ("calls", json!([])),
        ("payer", Value::Null),
        ("sponsor", Value::Null),
        ("auxiliaryData", json!([])),
        ("gasPrice", json!("0x0")),
        ("blobVersionedHashes", json!([])),
        ("maxFeePerBlobGas", json!("0x0")),
    ] {
        let mut request = serde_json::to_value(complete()).unwrap();
        request[field] = value;
        assert!(
            serde_json::from_value::<MonadTransactionRequest>(request).is_err(),
            "{field}"
        );
    }
}

#[test]
fn json_rejects_duplicate_fields_before_signing() {
    for json in [
        r#"{"type":"0x40","type":"0x2"}"#,
        r#"{"type":"0x40","nonce":"0x0","nonce":"0x1"}"#,
        r#"{"type":"0x40","accessList":[],"accessList":null}"#,
        r#"{"type":"0x40","maxFeePerGas":"0x1","maxFeePerGas":"0x2"}"#,
    ] {
        assert!(serde_json::from_str::<MonadTransactionRequest>(json).is_err());
    }
}

#[test]
fn native_builder_rejects_unsupported_rust_fields_and_fee_conflicts() {
    let mut auth = complete();
    auth.inner.authorization_list = Some(vec![]);
    let mut gas_price = complete();
    gas_price.inner.gas_price = Some(0);
    let mut blobs = complete();
    blobs.inner.blob_versioned_hashes = Some(vec![]);
    let mut blob_fee = complete();
    blob_fee.inner.max_fee_per_blob_gas = Some(0);
    let mut fees = complete();
    fees.inner.max_priority_fee_per_gas = Some(50_000_000_001);
    let mut unknown = complete();
    unknown.inner.transaction_type = Some(0x41);
    for request in [auth, gas_price, blobs, blob_fee, fees, unknown] {
        assert!(!request.can_build());
        assert!(request.build_unsigned().is_err());
    }
}

#[test]
fn json_and_builders_reject_disagreeing_input_aliases() {
    let mut request = complete();
    request.inner.input.input = Some(Bytes::from_static(&[1]));
    request.inner.input.data = Some(Bytes::from_static(&[2]));
    assert!(serde_json::from_value::<MonadTransactionRequest>(
        serde_json::to_value(&request).unwrap()
    )
    .is_err());
    assert!(request.build_unsigned().is_err());
}

#[test]
fn creation_access_list_presence_and_wide_values_survive_request_round_trips() {
    for access_list in [None, Some(Default::default())] {
        let tx = TxMonad {
            chain_id: 20143,
            to: TxKind::Create,
            access_list,
            value: U256::MAX,
            ..Default::default()
        };
        let request: MonadTransactionRequest = tx.clone().into();
        let request: MonadTransactionRequest =
            serde_json::from_value(serde_json::to_value(&request).unwrap()).unwrap();
        assert_eq!(
            request.build_unsigned().unwrap(),
            TypedTransaction::Monad(tx)
        );
    }
    let mut request = complete();
    request.inner.to = None;
    assert!(request.build_unsigned().unwrap().is_create());
}

#[test]
fn fee_and_chain_bounds_reject_overflow_without_narrowing_value() {
    let mut request = serde_json::to_value(complete()).unwrap();
    request["maxFeePerGas"] = json!(format!("0x{:x}", u128::MAX));
    request["maxPriorityFeePerGas"] = request["maxFeePerGas"].clone();
    request["chainId"] = json!(format!("0x{:x}", u64::MAX));
    request["value"] = json!(U256::MAX);
    let tx = serde_json::from_value::<MonadTransactionRequest>(request.clone())
        .unwrap()
        .build_unsigned()
        .unwrap();
    assert_eq!(tx.max_fee_per_gas(), u128::MAX);
    assert_eq!(tx.chain_id(), Some(u64::MAX));
    assert_eq!(tx.value(), U256::MAX);
    for (field, overflow) in [
        ("maxFeePerGas", "0x100000000000000000000000000000000"),
        (
            "maxPriorityFeePerGas",
            "0x100000000000000000000000000000000",
        ),
        ("chainId", "0x10000000000000000"),
    ] {
        let mut oversized = request.clone();
        oversized[field] = json!(overflow);
        assert!(serde_json::from_value::<MonadTransactionRequest>(oversized).is_err());
    }
}

#[test]
fn newly_signed_native_output_normalizes_high_s_and_recomputes_hash() {
    let tx = complete().build_unsigned().unwrap();
    let low = signer().sign_hash_sync(&tx.signature_hash()).unwrap();
    let order = U256::from_str_radix(
        "fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141",
        16,
    )
    .unwrap();
    let high = Signature::new(low.r(), order - low.s(), !low.v());
    let expected: TxEnvelope = tx.clone().into_signed(low).into();
    let actual: TxEnvelope = Signed::new_unchecked(tx, high, B256::ZERO).into();
    assert_eq!(actual, expected);
    assert_eq!(actual.recover_signer().unwrap(), signer().address());
}

#[test]
fn rpc_response_to_request_preserves_sender_and_native_commitment() {
    let native = complete().build_unsigned().unwrap();
    let sig = signer().sign_hash_sync(&native.signature_hash()).unwrap();
    let envelope: TxEnvelope = native.into_signed(sig).into();
    let response = monad_alloy::rpc::Transaction {
        inner: envelope.clone().try_into_recovered().unwrap(),
        effective_gas_price: Some(1),
        ..Default::default()
    };
    let request: MonadTransactionRequest = response.into();
    assert_eq!(request.inner.from, Some(signer().address()));
    assert_eq!(request.inner.gas_price, None);
    let rebuilt: TxEnvelope = request.build_unsigned().unwrap().into_signed(sig).into();
    assert_eq!(rebuilt, envelope);
}

#[tokio::test]
async fn ethereum_wallet_paths_preserve_types_and_hashes() {
    let wallet = EthereumWallet::from(signer());
    for ty in [0, 1, 2, 4] {
        let mut inner = alloy_rpc_types_eth::TransactionRequest {
            transaction_type: Some(ty),
            chain_id: Some(20143),
            nonce: Some(1),
            gas: Some(30_000),
            to: Some(Address::with_last_byte(2).into()),
            ..Default::default()
        };
        if ty <= 1 {
            inner.gas_price = Some(3);
        } else {
            inner.max_fee_per_gas = Some(3);
            inner.max_priority_fee_per_gas = Some(1);
        }
        if ty == 1 {
            inner.access_list = Some(Default::default());
        }
        if ty == 4 {
            inner.authorization_list = Some(vec![]);
        }
        let expected = inner.clone().build(&wallet).await.unwrap();
        let actual = MonadTransactionRequest { inner }
            .build(&wallet)
            .await
            .unwrap();
        assert_eq!(actual.ty(), ty);
        assert_eq!(actual.encoded_2718(), expected.encoded_2718());
        assert_eq!(actual.hash(), expected.hash());
    }
}
