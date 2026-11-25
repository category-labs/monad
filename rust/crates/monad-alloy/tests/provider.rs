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

use std::sync::{Arc, Mutex};

use alloy_consensus::{Receipt, SignableTransaction, Transaction};
use alloy_eips::{Decodable2718, Encodable2718, Typed2718};
use alloy_network::{EthereumWallet, NetworkTransactionBuilder, TransactionBuilder};
use alloy_primitives::{keccak256, Address, Bytes, B256};
use alloy_provider::Provider;
use alloy_signer::SignerSync;
use alloy_signer_local::PrivateKeySigner;
use monad_alloy::{
    provider_builder, rpc, MonadProviderExt, MonadTransactionRequest, ReceiptEnvelope, TxEnvelope,
};
use serde_json::{json, Value};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::TcpListener,
    task::JoinHandle,
};

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
fn signed() -> TxEnvelope {
    let tx = complete().build_unsigned().unwrap();
    let sig = signer().sign_hash_sync(&tx.signature_hash()).unwrap();
    tx.into_signed(sig).into()
}
fn submitted(request: &Value) -> TxEnvelope {
    let bytes: Bytes = serde_json::from_value(request["params"][0].clone()).unwrap();
    TxEnvelope::decode_submission(&bytes).unwrap()
}
fn receipt(tx: &TxEnvelope) -> Value {
    let inner: ReceiptEnvelope<alloy_rpc_types_eth::Log> =
        ReceiptEnvelope::Monad(Receipt::default().with_bloom());
    let mut result = serde_json::to_value(inner).unwrap();
    let object = result.as_object_mut().unwrap();
    object.extend(json!({
        "status":"0x1", "transactionHash":tx.hash(), "transactionIndex":"0x0",
        "blockHash":B256::with_last_byte(1), "blockNumber":"0x1", "gasUsed":"0x5208",
        "effectiveGasPrice":"0x77359400", "from":signer().address(), "to":Address::with_last_byte(2),
        "contractAddress":null
    }).as_object().unwrap().clone());
    result
}
fn transaction(tx: &TxEnvelope) -> rpc::Transaction {
    rpc::Transaction {
        native_execution: Default::default(),
        inner: tx.clone().try_into_recovered().unwrap(),
        block_hash: Some(B256::with_last_byte(1)),
        block_number: Some(1),
        transaction_index: Some(0),
        effective_gas_price: Some(2_000_000_000),
        block_timestamp: None,
    }
}

fn default_response(request: &Value) -> Result<Value, Value> {
    Ok(match request["method"].as_str().unwrap() {
        "eth_chainId" => json!("0x4eaf"),
        "eth_blockNumber" => json!("0x1"),
        "eth_getTransactionCount" => json!("0x7"),
        "eth_estimateGas" => json!("0x5208"),
        "eth_feeHistory" => {
            json!({"oldestBlock":"0x1","baseFeePerGas":["0x3b9aca00","0x3b9aca00"],"gasUsedRatio":[0.5],"reward":[["0x77359400"]]})
        }
        "eth_sendRawTransaction" => json!(submitted(request).hash()),
        "eth_sendRawTransactionSync" => receipt(&submitted(request)),
        method => {
            return Err(json!({"code":-32601,"message":format!("unexpected method {method}")}))
        }
    })
}

struct Server {
    url: String,
    requests: Arc<Mutex<Vec<Value>>>,
    task: JoinHandle<()>,
}
impl Drop for Server {
    fn drop(&mut self) {
        self.task.abort();
    }
}
impl Server {
    async fn new(respond: impl Fn(&Value) -> Result<Value, Value> + Send + Sync + 'static) -> Self {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let url = format!("http://{}", listener.local_addr().unwrap());
        let requests = Arc::new(Mutex::new(Vec::new()));
        let captured = requests.clone();
        let respond = Arc::new(respond);
        let task = tokio::spawn(async move {
            loop {
                let (mut socket, _) = listener.accept().await.unwrap();
                let captured = captured.clone();
                let respond = respond.clone();
                tokio::spawn(async move {
                    let mut data = Vec::new();
                    let header_end = loop {
                        let mut buf = [0u8; 4096];
                        let count = socket.read(&mut buf).await.unwrap();
                        if count == 0 {
                            return;
                        }
                        data.extend_from_slice(&buf[..count]);
                        if let Some(index) =
                            data.windows(4).position(|window| window == b"\r\n\r\n")
                        {
                            break index + 4;
                        }
                    };
                    let header = std::str::from_utf8(&data[..header_end]).unwrap();
                    let length: usize = header
                        .lines()
                        .find_map(|line| {
                            let (name, value) = line.split_once(':')?;
                            name.eq_ignore_ascii_case("content-length")
                                .then(|| value.trim().parse().unwrap())
                        })
                        .unwrap();
                    while data.len() < header_end + length {
                        let mut buf = [0u8; 4096];
                        let count = socket.read(&mut buf).await.unwrap();
                        assert_ne!(count, 0);
                        data.extend_from_slice(&buf[..count]);
                    }
                    let request: Value =
                        serde_json::from_slice(&data[header_end..header_end + length]).unwrap();
                    captured.lock().unwrap().push(request.clone());
                    let response = match respond(&request) {
                        Ok(result) => json!({"jsonrpc":"2.0","id":request["id"],"result":result}),
                        Err(error) => json!({"jsonrpc":"2.0","id":request["id"],"error":error}),
                    }
                    .to_string();
                    let wire = format!("HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}", response.len(), response);
                    socket.write_all(wire.as_bytes()).await.unwrap();
                });
            }
        });
        Self {
            url,
            requests,
            task,
        }
    }
    fn calls(&self, method: &str) -> Vec<Value> {
        self.requests
            .lock()
            .unwrap()
            .iter()
            .filter(|r| r["method"] == method)
            .cloned()
            .collect()
    }
}

#[tokio::test]
async fn local_wallet_submits_three_fields_and_returns_canonical_hash() {
    let server = Server::new(default_response).await;
    let provider = provider_builder()
        .wallet(EthereumWallet::from(signer()))
        .connect_http(server.url.parse().unwrap());
    let pending = provider.send_transaction(complete()).await.unwrap();
    assert_eq!(pending.tx_hash(), signed().hash());
    let calls = server.calls("eth_sendRawTransaction");
    assert_eq!(calls.len(), 1);
    let wire: Bytes = serde_json::from_value(calls[0]["params"][0].clone()).unwrap();
    assert!(TxEnvelope::decode_2718_exact(&wire).is_err());
    assert_eq!(submitted(&calls[0]).encoded_2718(), signed().encoded_2718());
    assert_ne!(keccak256(&wire), *pending.tx_hash());
    assert!(server.calls("eth_sendTransaction").is_empty());
}

#[tokio::test]
async fn native_type_survives_chain_nonce_gas_and_fee_filling() {
    let server = Server::new(default_response).await;
    let provider = provider_builder()
        .wallet(EthereumWallet::from(signer()))
        .connect_http(server.url.parse().unwrap());
    let _ = provider
        .send_transaction(MonadTransactionRequest::native().with_to(Address::with_last_byte(2)))
        .await
        .unwrap();
    let estimates = server.calls("eth_estimateGas");
    assert_eq!(estimates.len(), 1);
    assert_eq!(estimates[0]["params"][0]["type"], "0x40");
    let tx = submitted(&server.calls("eth_sendRawTransaction")[0]);
    assert_eq!(tx.ty(), 0x40);
    assert_eq!(tx.chain_id(), Some(20143));
    assert_eq!(tx.nonce(), 7);
    assert_eq!(tx.gas_limit(), 21_000);
    assert_eq!(tx.max_priority_fee_per_gas(), Some(2_000_000_000));
    assert_eq!(
        server.calls("eth_getTransactionCount")[0]["params"][1],
        "pending"
    );
}

#[tokio::test]
async fn native_fee_filling_preserves_either_explicit_cap() {
    for keep_max in [false, true] {
        let server = Server::new(default_response).await;
        let provider = provider_builder()
            .wallet(EthereumWallet::from(signer()))
            .connect_http(server.url.parse().unwrap());
        let mut request = complete();
        if keep_max {
            request.inner.max_priority_fee_per_gas = None;
        } else {
            request.inner.max_fee_per_gas = None;
            request.inner.max_priority_fee_per_gas = Some(123);
        }
        let _ = provider.send_transaction(request).await.unwrap();
        let tx = submitted(&server.calls("eth_sendRawTransaction")[0]);
        if keep_max {
            assert_eq!(tx.max_fee_per_gas(), 50_000_000_000);
        } else {
            assert_eq!(tx.max_priority_fee_per_gas(), Some(123));
        }
    }
}

#[tokio::test]
async fn native_fee_estimation_never_falls_back_to_legacy() {
    let server = Server::new(|request| {
        if request["method"] == "eth_feeHistory" {
            return Ok(
                json!({"oldestBlock":"0x1","baseFeePerGas":[],"gasUsedRatio":[],"reward":[]}),
            );
        }
        if request["method"] == "eth_getBlockByNumber" {
            let mut block = serde_json::to_value(<rpc::Block>::default()).unwrap();
            block.as_object_mut().unwrap().remove("baseFeePerGas");
            return Ok(block);
        }
        default_response(request)
    })
    .await;
    let provider = provider_builder()
        .wallet(EthereumWallet::from(signer()))
        .connect_http(server.url.parse().unwrap());
    let mut request = complete();
    request.inner.max_fee_per_gas = None;
    assert!(provider.send_transaction(request).await.is_err());
    assert!(server.calls("eth_gasPrice").is_empty());
    assert!(server.calls("eth_sendRawTransaction").is_empty());
}

#[tokio::test]
async fn raw_native_submission_bytes_pass_through_for_both_send_methods() {
    let server = Server::new(default_response).await;
    let provider = provider_builder().connect_http(server.url.parse().unwrap());
    let envelope = signed();
    let raw = envelope.encode_submission();
    assert_eq!(
        provider.send_raw_transaction(&raw).await.unwrap().tx_hash(),
        envelope.hash()
    );
    assert_eq!(
        provider
            .send_raw_transaction_sync(&raw)
            .await
            .unwrap()
            .transaction_hash,
        *envelope.hash()
    );
    for method in ["eth_sendRawTransaction", "eth_sendRawTransactionSync"] {
        let calls = server.calls(method);
        let actual: Bytes = serde_json::from_value(calls[0]["params"][0].clone()).unwrap();
        assert_eq!(actual.as_ref(), raw);
    }
}

#[tokio::test]
async fn presigned_envelope_path_uses_submission_encoding() {
    let server = Server::new(default_response).await;
    let provider = provider_builder().connect_http(server.url.parse().unwrap());
    assert_eq!(
        provider.send_tx_envelope(signed()).await.unwrap().tx_hash(),
        signed().hash()
    );
    assert_eq!(
        submitted(&server.calls("eth_sendRawTransaction")[0]),
        signed()
    );
}

#[tokio::test]
async fn synchronous_wallet_and_raw_paths_preserve_receipt_type_and_hash() {
    let server = Server::new(default_response).await;
    let provider = provider_builder()
        .wallet(EthereumWallet::from(signer()))
        .connect_http(server.url.parse().unwrap());
    let first = provider.send_transaction_sync(complete()).await.unwrap();
    let second = provider.send_tx_envelope_sync(signed()).await.unwrap();
    assert_eq!(first.transaction_hash, *signed().hash());
    assert_eq!(first.inner.ty(), 0x40);
    assert_eq!(first, second);
    assert_eq!(server.calls("eth_sendRawTransactionSync").len(), 2);
    assert!(server.calls("eth_sendTransactionSync").is_empty());
}

#[tokio::test]
async fn wrong_rpc_transaction_hash_and_wrong_sync_receipt_are_errors() {
    for wrong_type in [false, true] {
        let server = Server::new(move |request| {
            if request["method"] == "eth_sendRawTransaction" {
                return Ok(json!(B256::ZERO));
            }
            if request["method"] == "eth_sendRawTransactionSync" {
                let mut result = receipt(&submitted(request));
                if wrong_type {
                    result["type"] = json!("0x2");
                } else {
                    result["transactionHash"] = json!(B256::ZERO);
                }
                return Ok(result);
            }
            default_response(request)
        })
        .await;
        let provider = provider_builder().connect_http(server.url.parse().unwrap());
        assert!(provider.send_tx_envelope(signed()).await.is_err());
        assert!(provider.send_tx_envelope_sync(signed()).await.is_err());
    }
}

#[tokio::test]
async fn invalid_native_envelopes_never_reach_rpc() {
    use alloy_consensus::Signed;
    use alloy_primitives::{Signature, U256};
    let server = Server::new(default_response).await;
    let provider = provider_builder().connect_http(server.url.parse().unwrap());
    let tx = signed().as_monad().unwrap().tx().clone();
    let invalid_signature = TxEnvelope::Monad(Signed::new_unhashed(
        tx.clone(),
        Signature::new(U256::ZERO, U256::ZERO, false),
    ));
    let mut invalid_fee = tx;
    invalid_fee.max_priority_fee_per_gas = invalid_fee.max_fee_per_gas + 1;
    let signature = signer()
        .sign_hash_sync(&invalid_fee.signature_hash())
        .unwrap();
    let invalid_fee = TxEnvelope::Monad(invalid_fee.into_signed(signature));
    for tx in [invalid_signature, invalid_fee] {
        assert!(provider.send_tx_envelope(tx.clone()).await.is_err());
        assert!(provider.send_tx_envelope_sync(tx).await.is_err());
    }
    assert!(server.calls("eth_sendRawTransaction").is_empty());
    assert!(server.calls("eth_sendRawTransactionSync").is_empty());
}

#[tokio::test]
async fn native_requests_without_a_wallet_never_use_node_managed_signing() {
    let server = Server::new(default_response).await;
    let provider = provider_builder().connect_http(server.url.parse().unwrap());
    assert!(provider
        .send_transaction(complete())
        .await
        .unwrap_err()
        .to_string()
        .contains("local wallet"));
    assert!(provider
        .send_transaction_sync(complete())
        .await
        .unwrap_err()
        .to_string()
        .contains("local wallet"));
    assert!(server.calls("eth_sendTransaction").is_empty());
    assert!(server.calls("eth_sendTransactionSync").is_empty());
    assert!(server.calls("eth_sendRawTransaction").is_empty());
}

#[tokio::test]
async fn unknown_wallet_sender_is_rejected_without_submission() {
    let server = Server::new(default_response).await;
    let provider = provider_builder()
        .wallet(EthereumWallet::from(signer()))
        .connect_http(server.url.parse().unwrap());
    assert!(provider
        .send_transaction(complete().with_from(Address::with_last_byte(99)))
        .await
        .is_err());
    assert!(server.calls("eth_sendRawTransaction").is_empty());
}

#[tokio::test]
async fn ethereum_raw_bytes_are_forwarded_without_native_reinterpretation() {
    let server = Server::new(|request| {
        if request["method"] == "eth_sendRawTransaction" {
            return Ok(json!(B256::with_last_byte(9)));
        }
        default_response(request)
    })
    .await;
    let provider = provider_builder().connect_http(server.url.parse().unwrap());
    for bytes in [
        vec![0x02, 0xc0],
        vec![0x01, 0xc0],
        vec![0x03, 0xc0],
        vec![0x04, 0xc0],
        vec![0xc0],
    ] {
        let _ = provider.send_raw_transaction(&bytes).await.unwrap();
        let calls = server.calls("eth_sendRawTransaction");
        let actual: Bytes =
            serde_json::from_value(calls.last().unwrap()["params"][0].clone()).unwrap();
        assert_eq!(actual.as_ref(), bytes);
    }
}

#[tokio::test]
async fn typed_transaction_receipt_and_full_block_reads_keep_native_identity() {
    let server = Server::new(|request| {
        let tx = signed();
        match request["method"].as_str().unwrap() {
            "eth_getTransactionByHash" => Ok(serde_json::to_value(transaction(&tx)).unwrap()),
            "eth_getTransactionReceipt" => Ok(receipt(&tx)),
            "eth_getBlockByNumber" => {
                let mut block = serde_json::to_value(<rpc::Block>::default()).unwrap();
                block["transactions"] = json!([transaction(&tx)]);
                block["hash"] = json!(B256::with_last_byte(1));
                block["number"] = json!("0x1");
                Ok(block)
            }
            _ => default_response(request),
        }
    })
    .await;
    let provider = provider_builder().connect_http(server.url.parse().unwrap());
    let tx = provider
        .get_transaction_by_hash(*signed().hash())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(tx.inner.inner().ty(), 0x40);
    assert_eq!(tx.inner.tx_hash(), signed().hash());
    assert!(tx.canonical_envelope().is_err());
    assert_eq!(tx.calls().unwrap().unwrap().len(), 1);
    let receipt = provider
        .get_transaction_receipt(*signed().hash())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(receipt.inner.ty(), 0x40);
    assert_eq!(receipt.transaction_hash, *signed().hash());
    let block = provider
        .get_block_by_number(1.into())
        .full()
        .await
        .unwrap()
        .unwrap();
    let included = block.transactions.as_transactions().unwrap();
    assert_eq!(included.len(), 1);
    assert_eq!(included[0].inner.tx_hash(), signed().hash());
    assert!(included[0].canonical_envelope().is_err());
}
