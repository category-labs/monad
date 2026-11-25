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
use alloy_eips::{eip2930::AccessList, eip7702::SignedAuthorization, Typed2718};
use alloy_primitives::{Bytes, Signature, TxKind, B256, U256};
use alloy_rlp::BufMut;

use crate::{TxEnvelope, TxMonad};

/// Unsigned transactions accepted by the shared envelope and Alloy wallets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedTransaction {
    Ethereum(alloy_consensus::TypedTransaction),
    Monad(TxMonad),
}

impl TypedTransaction {
    fn transaction(&self) -> &dyn Transaction {
        match self {
            Self::Ethereum(tx) => tx,
            Self::Monad(tx) => tx,
        }
    }

    fn signable(&self) -> &dyn SignableTransaction<Signature> {
        match self {
            Self::Ethereum(tx) => tx,
            Self::Monad(tx) => tx,
        }
    }
}

impl From<TxMonad> for TypedTransaction {
    fn from(tx: TxMonad) -> Self {
        Self::Monad(tx)
    }
}

impl From<alloy_consensus::TypedTransaction> for TypedTransaction {
    fn from(tx: alloy_consensus::TypedTransaction) -> Self {
        Self::Ethereum(tx)
    }
}

impl From<TxEnvelope> for TypedTransaction {
    fn from(tx: TxEnvelope) -> Self {
        match tx {
            TxEnvelope::Legacy(tx) => Self::Ethereum(tx.strip_signature().into()),
            TxEnvelope::Eip2930(tx) => Self::Ethereum(tx.strip_signature().into()),
            TxEnvelope::Eip1559(tx) => Self::Ethereum(tx.strip_signature().into()),
            TxEnvelope::Eip4844(tx) => Self::Ethereum(tx.strip_signature().into()),
            TxEnvelope::Eip7702(tx) => Self::Ethereum(tx.strip_signature().into()),
            TxEnvelope::Monad(tx) => Self::Monad(tx.strip_signature()),
        }
    }
}

impl From<Signed<TypedTransaction>> for TxEnvelope {
    fn from(signed: Signed<TypedTransaction>) -> Self {
        let signature = *signed.signature();
        match signed.strip_signature() {
            TypedTransaction::Ethereum(tx) => tx.into_envelope(signature).into(),
            TypedTransaction::Monad(tx) => {
                // Normalize newly signed output, never bytes received by a decoder.
                let signature = signature.normalize_s().unwrap_or(signature);
                Self::Monad(tx.into_signed(signature))
            }
        }
    }
}

impl Typed2718 for TypedTransaction {
    fn ty(&self) -> u8 {
        self.transaction().ty()
    }
}

impl Transaction for TypedTransaction {
    fn chain_id(&self) -> Option<u64> {
        self.transaction().chain_id()
    }
    fn nonce(&self) -> u64 {
        self.transaction().nonce()
    }
    fn gas_limit(&self) -> u64 {
        self.transaction().gas_limit()
    }
    fn gas_price(&self) -> Option<u128> {
        self.transaction().gas_price()
    }
    fn max_fee_per_gas(&self) -> u128 {
        self.transaction().max_fee_per_gas()
    }
    fn max_priority_fee_per_gas(&self) -> Option<u128> {
        self.transaction().max_priority_fee_per_gas()
    }
    fn max_fee_per_blob_gas(&self) -> Option<u128> {
        self.transaction().max_fee_per_blob_gas()
    }
    fn priority_fee_or_price(&self) -> u128 {
        self.transaction().priority_fee_or_price()
    }
    fn effective_gas_price(&self, base_fee: Option<u64>) -> u128 {
        self.transaction().effective_gas_price(base_fee)
    }
    fn is_dynamic_fee(&self) -> bool {
        self.transaction().is_dynamic_fee()
    }
    fn kind(&self) -> TxKind {
        self.transaction().kind()
    }
    fn is_create(&self) -> bool {
        self.transaction().is_create()
    }
    fn value(&self) -> U256 {
        self.transaction().value()
    }
    fn input(&self) -> &Bytes {
        self.transaction().input()
    }
    fn access_list(&self) -> Option<&AccessList> {
        self.transaction().access_list()
    }
    fn blob_versioned_hashes(&self) -> Option<&[B256]> {
        self.transaction().blob_versioned_hashes()
    }
    fn authorization_list(&self) -> Option<&[SignedAuthorization]> {
        self.transaction().authorization_list()
    }
}

impl SignableTransaction<Signature> for TypedTransaction {
    fn set_chain_id(&mut self, chain_id: u64) {
        match self {
            Self::Ethereum(tx) => tx.set_chain_id(chain_id),
            Self::Monad(tx) => tx.set_chain_id(chain_id),
        }
    }
    fn encode_for_signing(&self, out: &mut dyn BufMut) {
        self.signable().encode_for_signing(out);
    }
    fn payload_len_for_signature(&self) -> usize {
        self.signable().payload_len_for_signature()
    }
}
