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

use alloy_eips::Encodable2718;
use alloy_primitives::{keccak256, B256};
use alloy_provider::{
    fillers::JoinFill, Identity, PendingTransactionBuilder, Provider, ProviderBuilder,
    ProviderLayer, RootProvider, SendableTx, Stack,
};
use alloy_transport::{TransportErrorKind, TransportResult};
use monad_transaction::{rpc, TxEnvelope, TxType};

use crate::{MonadFillers, MonadNetwork};

/// Install below Alloy's fillers so envelopes are signed before submission adaptation.
#[derive(Clone, Copy, Debug, Default)]
pub struct MonadLayer;

impl<P: Provider<MonadNetwork>> ProviderLayer<P, MonadNetwork> for MonadLayer {
    type Provider = MonadProvider<P>;
    fn layer(&self, inner: P) -> Self::Provider {
        MonadProvider { inner }
    }
}

/// An Alloy provider with native submission encoding and canonical hash checks.
#[derive(Clone, Debug)]
pub struct MonadProvider<P> {
    inner: P,
}

pub type MonadProviderBuilder =
    ProviderBuilder<Stack<MonadLayer, Identity>, JoinFill<Identity, MonadFillers>, MonadNetwork>;

/// Construct a provider with gas, nonce, chain ID, and native submission support.
/// Add `.wallet(EthereumWallet::from(signer))` for local signing.
pub fn provider_builder() -> MonadProviderBuilder {
    ProviderBuilder::<Identity, Identity, MonadNetwork>::default()
        .with_recommended_fillers()
        .layer(MonadLayer)
}

fn checked_submission(envelope: &TxEnvelope) -> TransportResult<(Vec<u8>, Option<B256>)> {
    let Some(tx) = envelope.as_monad() else {
        return Ok((envelope.encode_submission(), None));
    };
    envelope
        .recover_signer()
        .map_err(TransportErrorKind::custom)?;
    if tx.tx().max_priority_fee_per_gas > tx.tx().max_fee_per_gas {
        return Err(TransportErrorKind::custom_str(
            "maxPriorityFeePerGas exceeds maxFeePerGas",
        ));
    }
    // Compute from canonical bytes, including for manually constructed Signed values.
    Ok((
        envelope.encode_submission(),
        Some(keccak256(envelope.encoded_2718())),
    ))
}

/// Signed-envelope synchronous submission, available on every Monad provider.
/// Raw RPC methods retain Alloy's literal-byte semantics: pass `encode_submission()`.
#[cfg_attr(target_family = "wasm", async_trait::async_trait(?Send))]
#[cfg_attr(not(target_family = "wasm"), async_trait::async_trait)]
pub trait MonadProviderExt: Provider<MonadNetwork> {
    async fn send_tx_envelope_sync(
        &self,
        tx: TxEnvelope,
    ) -> TransportResult<rpc::TransactionReceipt> {
        let (wire, expected_hash) = checked_submission(&tx)?;
        let receipt = self.send_raw_transaction_sync(&wire).await?;
        if let Some(expected_hash) = expected_hash {
            if receipt.transaction_hash != expected_hash || receipt.inner.tx_type() != TxType::Monad
            {
                return Err(TransportErrorKind::custom_str(&format!(
                    "RPC returned an inconsistent receipt for native transaction {expected_hash}"
                )));
            }
        }
        Ok(receipt)
    }
}
impl<P: Provider<MonadNetwork> + ?Sized> MonadProviderExt for P {}

#[cfg_attr(target_family = "wasm", async_trait::async_trait(?Send))]
#[cfg_attr(not(target_family = "wasm"), async_trait::async_trait)]
impl<P: Provider<MonadNetwork>> Provider<MonadNetwork> for MonadProvider<P> {
    fn root(&self) -> &RootProvider<MonadNetwork> {
        self.inner.root()
    }

    async fn send_transaction_internal(
        &self,
        tx: SendableTx<MonadNetwork>,
    ) -> TransportResult<PendingTransactionBuilder<MonadNetwork>> {
        match tx {
            SendableTx::Envelope(tx) if tx.is_monad() => {
                let (wire, expected_hash) = checked_submission(&tx)?;
                let pending = self.inner.send_raw_transaction(&wire).await?;
                if Some(*pending.tx_hash()) != expected_hash {
                    return Err(TransportErrorKind::custom_str(&format!(
                        "RPC returned hash {} for native transaction {}",
                        pending.tx_hash(),
                        expected_hash.expect("native envelope")
                    )));
                }
                Ok(pending)
            }
            SendableTx::Builder(ref request) if request.is_native() => {
                Err(TransportErrorKind::custom_str(
                    "native transactions require a local wallet; configure the wallet filler",
                ))
            }
            other => self.inner.send_transaction_internal(other).await,
        }
    }

    async fn send_transaction_sync_internal(
        &self,
        tx: SendableTx<MonadNetwork>,
    ) -> TransportResult<rpc::TransactionReceipt> {
        match tx {
            SendableTx::Envelope(tx) if tx.is_monad() => self.inner.send_tx_envelope_sync(tx).await,
            SendableTx::Builder(ref request) if request.is_native() => {
                Err(TransportErrorKind::custom_str(
                    "native transactions require a local wallet; configure the wallet filler",
                ))
            }
            other => self.inner.send_transaction_sync_internal(other).await,
        }
    }
}
