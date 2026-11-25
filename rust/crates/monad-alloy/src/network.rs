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

use alloy_network::Network;
use monad_transaction::{rpc, ReceiptEnvelope, TxEnvelope, TxType, TypedTransaction};

use crate::MonadTransactionRequest;

/// Monad RPC types, including the phase-0 native transaction and receipt.
/// Use [`crate::provider_builder`] to install native submission encoding as well.
#[derive(Clone, Copy, Debug, Default)]
pub struct MonadNetwork;

impl Network for MonadNetwork {
    type TxType = TxType;
    type TxEnvelope = TxEnvelope;
    type UnsignedTx = TypedTransaction;
    type ReceiptEnvelope = ReceiptEnvelope;
    type Header = alloy_consensus::Header;
    type TransactionRequest = MonadTransactionRequest;
    type TransactionResponse = rpc::Transaction;
    type ReceiptResponse = rpc::TransactionReceipt;
    type HeaderResponse = alloy_rpc_types_eth::Header;
    type BlockResponse = rpc::Block;
}
