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

use alloy_consensus::{
    transaction::SignerRecoverable, Signed, TransactionEnvelope, TxEip1559, TxEip2930, TxEip7702,
    TxEnvelope, TxLegacy,
};
use alloy_primitives::{Address, Signature, B256};

/// Monad's EIP-2718 transaction envelope. Mirrors `alloy_consensus::TxEnvelope`
/// minus EIP-4844 (unsupported on Monad), with room to add Monad-specific variants.
#[derive(Clone, Debug, TransactionEnvelope)]
#[envelope(tx_type_name = MonadTxType, typed = MonadTypedTransaction)]
pub enum MonadTxEnvelope {
    #[envelope(ty = 0)]
    Legacy(Signed<TxLegacy>),
    #[envelope(ty = 1)]
    Eip2930(Signed<TxEip2930>),
    #[envelope(ty = 2)]
    Eip1559(Signed<TxEip1559>),
    #[envelope(ty = 4)]
    Eip7702(Signed<TxEip7702>),
}

impl MonadTxEnvelope {
    /// Calculate the signing hash for the transaction.
    pub fn signature_hash(&self) -> B256 {
        match self {
            Self::Legacy(tx) => tx.signature_hash(),
            Self::Eip2930(tx) => tx.signature_hash(),
            Self::Eip1559(tx) => tx.signature_hash(),
            Self::Eip7702(tx) => tx.signature_hash(),
        }
    }

    /// Return the reference to signature.
    pub const fn signature(&self) -> &Signature {
        match self {
            Self::Legacy(tx) => tx.signature(),
            Self::Eip2930(tx) => tx.signature(),
            Self::Eip1559(tx) => tx.signature(),
            Self::Eip7702(tx) => tx.signature(),
        }
    }

    /// Return the hash of the inner Signed.
    pub fn tx_hash(&self) -> &B256 {
        match self {
            Self::Legacy(tx) => tx.hash(),
            Self::Eip2930(tx) => tx.hash(),
            Self::Eip1559(tx) => tx.hash(),
            Self::Eip7702(tx) => tx.hash(),
        }
    }

    /// Reference to transaction hash. Used to identify transaction.
    pub fn hash(&self) -> &B256 {
        match self {
            Self::Legacy(tx) => tx.hash(),
            Self::Eip2930(tx) => tx.hash(),
            Self::Eip1559(tx) => tx.hash(),
            Self::Eip7702(tx) => tx.hash(),
        }
    }

    /// Returns the [`TxLegacy`] variant if the transaction is a legacy transaction.
    pub const fn as_legacy(&self) -> Option<&Signed<TxLegacy>> {
        match self {
            Self::Legacy(tx) => Some(tx),
            _ => None,
        }
    }

    /// Returns the [`TxEip2930`] variant if the transaction is an EIP-2930 transaction.
    pub const fn as_eip2930(&self) -> Option<&Signed<TxEip2930>> {
        match self {
            Self::Eip2930(tx) => Some(tx),
            _ => None,
        }
    }

    /// Returns the [`TxEip1559`] variant if the transaction is an EIP-1559 transaction.
    pub const fn as_eip1559(&self) -> Option<&Signed<TxEip1559>> {
        match self {
            Self::Eip1559(tx) => Some(tx),
            _ => None,
        }
    }

    /// Returns the [`TxEip7702`] variant if the transaction is an EIP-7702 transaction.
    pub const fn as_eip7702(&self) -> Option<&Signed<TxEip7702>> {
        match self {
            Self::Eip7702(tx) => Some(tx),
            _ => None,
        }
    }

    /// Return the length of the inner txn, including type byte length.
    pub fn eip2718_encoded_length(&self) -> usize {
        match self {
            Self::Legacy(t) => t.eip2718_encoded_length(),
            Self::Eip2930(t) => t.eip2718_encoded_length(),
            Self::Eip1559(t) => t.eip2718_encoded_length(),
            Self::Eip7702(t) => t.eip2718_encoded_length(),
        }
    }
}

impl SignerRecoverable for MonadTxEnvelope {
    fn recover_signer(&self) -> Result<Address, alloy_consensus::crypto::RecoveryError> {
        match self {
            Self::Legacy(tx) => SignerRecoverable::recover_signer(tx),
            Self::Eip2930(tx) => SignerRecoverable::recover_signer(tx),
            Self::Eip1559(tx) => SignerRecoverable::recover_signer(tx),
            Self::Eip7702(tx) => SignerRecoverable::recover_signer(tx),
        }
    }

    fn recover_signer_unchecked(&self) -> Result<Address, alloy_consensus::crypto::RecoveryError> {
        match self {
            Self::Legacy(tx) => SignerRecoverable::recover_signer_unchecked(tx),
            Self::Eip2930(tx) => SignerRecoverable::recover_signer_unchecked(tx),
            Self::Eip1559(tx) => SignerRecoverable::recover_signer_unchecked(tx),
            Self::Eip7702(tx) => SignerRecoverable::recover_signer_unchecked(tx),
        }
    }

    fn recover_with_buf(
        &self,
        buf: &mut Vec<u8>,
    ) -> Result<Address, alloy_consensus::crypto::RecoveryError> {
        match self {
            Self::Legacy(tx) => SignerRecoverable::recover_with_buf(tx, buf),
            Self::Eip2930(tx) => SignerRecoverable::recover_with_buf(tx, buf),
            Self::Eip1559(tx) => SignerRecoverable::recover_with_buf(tx, buf),
            Self::Eip7702(tx) => SignerRecoverable::recover_with_buf(tx, buf),
        }
    }

    fn recover_unchecked_with_buf(
        &self,
        buf: &mut Vec<u8>,
    ) -> Result<Address, alloy_consensus::crypto::RecoveryError> {
        match self {
            Self::Legacy(tx) => SignerRecoverable::recover_unchecked_with_buf(tx, buf),
            Self::Eip2930(tx) => SignerRecoverable::recover_unchecked_with_buf(tx, buf),
            Self::Eip1559(tx) => SignerRecoverable::recover_unchecked_with_buf(tx, buf),
            Self::Eip7702(tx) => SignerRecoverable::recover_unchecked_with_buf(tx, buf),
        }
    }
}

impl From<Signed<TxLegacy>> for MonadTxEnvelope {
    fn from(tx: Signed<TxLegacy>) -> Self {
        Self::Legacy(tx)
    }
}

impl From<Signed<TxEip2930>> for MonadTxEnvelope {
    fn from(tx: Signed<TxEip2930>) -> Self {
        Self::Eip2930(tx)
    }
}

impl From<Signed<TxEip1559>> for MonadTxEnvelope {
    fn from(tx: Signed<TxEip1559>) -> Self {
        Self::Eip1559(tx)
    }
}

impl From<Signed<TxEip7702>> for MonadTxEnvelope {
    fn from(tx: Signed<TxEip7702>) -> Self {
        Self::Eip7702(tx)
    }
}

impl From<MonadTxEnvelope> for TxEnvelope {
    fn from(tx: MonadTxEnvelope) -> Self {
        match tx {
            MonadTxEnvelope::Legacy(tx) => Self::Legacy(tx),
            MonadTxEnvelope::Eip2930(tx) => Self::Eip2930(tx),
            MonadTxEnvelope::Eip1559(tx) => Self::Eip1559(tx),
            MonadTxEnvelope::Eip7702(tx) => Self::Eip7702(tx),
        }
    }
}

/// Returned when a [`TxEnvelope`] contains a variant that [`MonadTxEnvelope`]
/// cannot represent (currently only EIP-4844).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnsupportedTxType;

impl std::fmt::Display for UnsupportedTxType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("transaction type not supported by MonadTxEnvelope")
    }
}

impl std::error::Error for UnsupportedTxType {}

impl TryFrom<TxEnvelope> for MonadTxEnvelope {
    type Error = UnsupportedTxType;

    fn try_from(tx: TxEnvelope) -> Result<Self, Self::Error> {
        match tx {
            TxEnvelope::Legacy(tx) => Ok(Self::Legacy(tx)),
            TxEnvelope::Eip2930(tx) => Ok(Self::Eip2930(tx)),
            TxEnvelope::Eip1559(tx) => Ok(Self::Eip1559(tx)),
            TxEnvelope::Eip7702(tx) => Ok(Self::Eip7702(tx)),
            TxEnvelope::Eip4844(_) => Err(UnsupportedTxType),
        }
    }
}
