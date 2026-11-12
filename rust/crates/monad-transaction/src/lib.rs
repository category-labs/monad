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

//! Canonical transaction identity is independent of the RPC submission wrapper.
//! Native fee quantities retain their full 256-bit width through consensus and RPC.

mod envelope;
mod framing;
mod native;
mod receipt;
pub mod rpc;
pub use envelope::{TxEnvelope, TxType};
pub use native::TxMonad;
pub use receipt::ReceiptEnvelope;

/// Universal transaction type selected by the main transaction design.
pub const MONAD_TX_TYPE: u8 = 0x40;
/// This experimental transaction profile is enabled only on a fresh development chain.
pub const MONAD_DEVNET_CHAIN_ID: u64 = 20143;
