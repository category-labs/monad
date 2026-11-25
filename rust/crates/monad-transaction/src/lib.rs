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

//! Canonical transaction identity is independent of the RPC submission wrapper.
//! Native fees use u128 and outer chain IDs use u64; values and accounting remain U256.

mod envelope;
mod framing;
mod native;
mod receipt;
pub mod rpc;
mod typed;
pub use envelope::{TxEnvelope, TxType};
pub use native::{validate_batch, MonadCall, TxMonad};
pub use receipt::ReceiptEnvelope;
pub use typed::TypedTransaction;

/// Universal transaction type selected by the main transaction design.
pub const MONAD_TX_TYPE: u8 = 0x40;
/// Feature registry key for the ordered, atomic call list.
pub const MONAD_CALLS_FEATURE: u8 = 0x08;
/// Intrinsic gas for each entry after the first.
pub const MONAD_CALL_ENTRY_GAS: u64 = 21_000;
/// Chain ID of the standard Monad development network.
pub const MONAD_DEVNET_CHAIN_ID: u64 = 20143;
