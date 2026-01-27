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

#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]
#![deny(rustdoc::private_intra_doc_links)]

//! Idiomatic and safe types for interacting with `monad` execution event rings.
//!
//! # Quickstart
//!
//! Add `monad-event-ring` and `monad-exec-events` as dependencies to your Cargo.toml.
//!
//! ```custom
//! cargo add --git https://github.com/monad-crypto/monad-bft monad-event-ring monad-exec-events
//! ```
//!
//! Next, create an event ring and start consuming events!
//!
//! ```no_run
//! # use monad_event_ring::{DecodedEventRing, EventDescriptor, EventPayloadResult, EventNextResult};
//! # use monad_exec_events::{ExecEventRing};
//! #
//! # let event_ring_path: &'static str = unimplemented!();
//! #
//! let event_ring = ExecEventRing::new_from_path(event_ring_path).unwrap();
//!
//! let mut event_reader = event_ring.create_reader();
//!
//! loop {
//!     let event_descriptor = match event_reader.next_descriptor() {
//!         EventNextResult::Gap => {
//!             // Handle EventRing gap!
//!             unimplemented!();
//!         }
//!         EventNextResult::NotReady => {
//!             // This will busy-wait until an event is ready.
//!             continue;
//!         }
//!         EventNextResult::Ready(event_descriptor) => event_descriptor,
//!     };
//!
//!     match event_descriptor.try_read() {
//!         EventPayloadResult::Expired => {
//!             // Handle EventRing payload expiry (similar to gap)!
//!             unimplemented!();
//!         }
//!         EventPayloadResult::Ready(exec_event) => {
//!             // Do something with the event!
//!         }
//!     }
//! }
//! ```
//!
//!
//! For more details about EventRing operation in general, see the
//! [`monad_event_ring`](../monad_event_ring/index.html) library documentation.
//!
//! # Block-Oriented Updates
//!
//! `EventRing`s using an [`ExecEventDecoder`] (primarily [`ExecEventRing`]) can produce individual
//! `monad` execution events. While many applications may benefit from operating on individual
//! events or by observing them as quickly as possible, many would prefer to process entire blocks.
//! This library provides the [`ExecutedBlockBuilder`] utility to reconstruct blocks from an event
//! stream produced by an [`ExecEventRing`]. See [`ExecutedBlockBuilder`] for more details.
//!
//! This utility however produces all blocks that are executed, which could be in any
//! [`BlockCommitState`]. For applications interested in consuming blocks once they have reached a
//! certain commit state, usually [`BlockCommitState::Finalized`], applications can use the
//! [`CommitStateBlockBuilder`] which produces a block along with its current commit state every time
//! the block's commit state changes. See [`CommitStateBlockBuilder`] for more details.

use monad_event_ring::{EventRing, SnapshotEventRing};

pub use self::{block::*, block_builder::*, events::*};

mod block;
mod block_builder;
mod events;
pub mod ffi;

/// A type alias for an event ring that produces monad execution events.
pub type ExecEventRing = EventRing<ExecEventDecoder>;

/// A type alias for a snapshot event ring that produces monad execution events.
pub type ExecSnapshotEventRing = SnapshotEventRing<ExecEventDecoder>;
