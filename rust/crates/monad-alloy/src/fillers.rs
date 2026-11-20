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

use alloy_provider::{
    fillers::{
        ChainIdFiller, FillerControlFlow, GasFillable, GasFiller, JoinFill, NonceFiller,
        RecommendedFillers, TxFiller,
    },
    utils::Eip1559Estimation,
    Provider, SendableTx,
};
use alloy_transport::{TransportErrorKind, TransportResult};

use crate::{MonadNetwork, MonadTransactionRequest};

/// Native requests retain explicit fee caps and never fall back to legacy fees.
#[derive(Clone, Debug, Default)]
pub struct MonadGasFiller {
    ethereum: GasFiller,
}

pub type MonadFillers = JoinFill<MonadGasFiller, JoinFill<NonceFiller, ChainIdFiller>>;

impl RecommendedFillers for MonadNetwork {
    type RecommendedFillers = MonadFillers;
    fn recommended_fillers() -> Self::RecommendedFillers {
        Default::default()
    }
}

impl TxFiller<MonadNetwork> for MonadGasFiller {
    type Fillable = GasFillable;

    fn status(&self, tx: &MonadTransactionRequest) -> FillerControlFlow {
        <GasFiller as TxFiller<MonadNetwork>>::status(&self.ethereum, tx)
    }
    fn fill_sync(&self, _tx: &mut SendableTx<MonadNetwork>) {}

    async fn prepare<P: Provider<MonadNetwork>>(
        &self,
        provider: &P,
        tx: &MonadTransactionRequest,
    ) -> TransportResult<Self::Fillable> {
        tx.validate().map_err(TransportErrorKind::custom_str)?;
        if !tx.is_native() {
            return self.ethereum.prepare(provider, tx).await;
        }
        let gas_limit = match tx.inner.gas {
            Some(gas) => gas,
            None => provider.estimate_gas(tx.clone()).await?,
        };
        let estimate = match (tx.inner.max_fee_per_gas, tx.inner.max_priority_fee_per_gas) {
            (Some(max_fee_per_gas), Some(max_priority_fee_per_gas)) => Eip1559Estimation {
                max_fee_per_gas,
                max_priority_fee_per_gas,
            },
            _ => {
                let estimate = provider.estimate_eip1559_fees().await?;
                Eip1559Estimation {
                    max_fee_per_gas: tx.inner.max_fee_per_gas.unwrap_or(estimate.max_fee_per_gas),
                    max_priority_fee_per_gas: tx
                        .inner
                        .max_priority_fee_per_gas
                        .unwrap_or(estimate.max_priority_fee_per_gas),
                }
            }
        };
        if estimate.max_priority_fee_per_gas > estimate.max_fee_per_gas {
            return Err(TransportErrorKind::custom_str(
                "filled maxPriorityFeePerGas exceeds maxFeePerGas",
            ));
        }
        Ok(GasFillable::Eip1559 {
            gas_limit,
            estimate,
        })
    }

    async fn fill(
        &self,
        fillable: Self::Fillable,
        tx: SendableTx<MonadNetwork>,
    ) -> TransportResult<SendableTx<MonadNetwork>> {
        self.ethereum.fill(fillable, tx).await
    }
}
