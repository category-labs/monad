# Monad Alloy client

`monad-alloy` integrates phase-0 native transactions with Alloy 2.0.4. It provides `MonadNetwork`, `MonadTransactionRequest` and `provider_builder()`, while reusing Alloy's `EthereumWallet`, signers, nonce/chain fillers and transports. It does not require changes to upstream Alloy.

Use the standard Alloy traits and matching Alloy dependencies in an application. This example also needs `alloy-network`, `alloy-provider`, `alloy-signer-local`, `alloy-primitives` and Tokio. The workspace lockfile records the tested versions.

```no_run
use alloy_network::{EthereumWallet, TransactionBuilder};
use alloy_primitives::U256;
use alloy_provider::Provider;
use alloy_signer_local::PrivateKeySigner;
use monad_alloy::{provider_builder, MonadTransactionRequest};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let signer: PrivateKeySigner = std::env::var("PRIVATE_KEY")?.parse()?;
    let provider = provider_builder()
        .wallet(EthereumWallet::from(signer))
        .connect_http(std::env::var("RPC_URL")?.parse()?);

    let request = MonadTransactionRequest::native()
        .with_chain_id(20143)
        .with_to(std::env::var("RECIPIENT")?.parse()?)
        .with_value(U256::from(1));
    let receipt = provider.send_transaction(request).await?.get_receipt().await?;
    println!("{}", receipt.transaction_hash);
    Ok(())
}
```

Use a disposable, funded devnet account. The provider fills missing nonce, gas and EIP-1559-style fee caps, signs the canonical payload and sends the three-field submission. Explicitly supplied fee caps are preserved; missing native fees never fall back to `gasPrice`. Fee caps use uint128, chain IDs/gas/nonce use uint64, and value uses uint256. An omitted destination means contract creation.

`MonadTransactionRequest::default()` retains Ethereum inference. Only `native()` or an explicit `type: "0x40"` selects native encoding. Unsupported native fields, conflicting `input`/`data`, duplicate JSON fields, invalid fee ordering and overflow are rejected. Native requests require local wallet signing or a signed envelope; the adapter does not invoke node-managed native signing.

## Submission methods

Always construct a sending provider with `provider_builder()`. Merely using `ProviderBuilder::network::<MonadNetwork>()` selects response/request types but does not install the submission adapter.

| Method | Input | Native behavior |
| --- | --- | --- |
| `send_transaction(request)` | Request plus wallet filler | Fills/signs, adds empty auxiliary list, checks the returned canonical hash. |
| `send_tx_envelope(envelope)` | Signed `TxEnvelope` | Validates signature and fee ordering, adds empty auxiliary list, checks the returned canonical hash. |
| `send_transaction_sync(request)` | Request plus wallet filler | Same adaptation, then checks native receipt type and canonical hash. |
| `MonadProviderExt::send_tx_envelope_sync(envelope)` | Signed `TxEnvelope` | Same adaptation and synchronous receipt checks. |
| `send_raw_transaction(bytes)` / `send_raw_transaction_sync(bytes)` | Ready-to-submit RPC bytes | Literal passthrough, following Alloy's raw-byte contract. Call `envelope.encode_submission()` first. No adapter hash check. |

The raw methods intentionally accept already prepared bytes. Passing `encoded_2718()` for a native transaction to a raw method sends the wrong two-field form and the node rejects it. `encoded_2718()` remains correct for hashing, blocks and storage. `encode_submission()` is identical to `encoded_2718()` for Ethereum envelopes.

Alloy 2.0.4's filler provider does not forward raw synchronous sends through an inner provider override. The adapter therefore handles wallet/signed-envelope sends and leaves both raw methods literal; it does not patch Alloy internals. This is covered by HTTP regressions for both raw methods.

Hash and receipt-type checks detect an inconsistent RPC response; they are not state or inclusion proofs. An RPC may have accepted a transaction before a response-validation error, so use the locally computed canonical hash to check its status before resubmitting.

## Reading

The provider returns `monad_transaction::rpc` aliases of Alloy's generic transaction, receipt and block types. These accept both Ethereum variants and native `0x40`; JSON still uses familiar Ethereum fields. Native transactions remain type `0x40` in full block responses, and the receipt also retains `0x40`.

The [read-only example](examples/inspect.rs) retrieves a transaction, recomputes its canonical hash, checks sender recovery, and compares its receipt and full-block entry. It does not send a transaction or use a private key.

See the [workspace guide](../../README.md) for protocol scope, execution-repository ownership and node integration.
