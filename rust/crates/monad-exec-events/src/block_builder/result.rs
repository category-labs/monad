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

use crate::ffi::monad_exec_block_start;

/// Result produced by a block builder while attempting to reassemble a block from execution events.
pub type BlockBuilderResult<T> = Result<T, BlockBuilderError>;

/// Error produced by a block builder while attempting to reassemble a block from execution events.
pub enum BlockBuilderError {
    /// The block was rejected by execution.
    Rejected,

    /// The payload expired while reading the event.
    PayloadExpired,

    /// The block cannot be correctly reassembled.
    ///
    /// This variant is produced when the [`ExecutedBlockBuilder`](crate::ExecutedBlockBuilder) is
    /// not given the entire sequential stream of event descriptors containing execution events from
    /// some block's initial [`monad_exec_block_start`] event to the final
    /// [`monad_exec_block_end`](crate::ffi::monad_exec_block_end) event. This can occur if
    /// the user skips, duplicates, or reorders event descriptors or, even worse, provides event
    /// descriptors from different event rings. The most likely of these scenarios arises if the
    /// upstream event ring gaps and
    /// [`ExecutedBlockBuilder::reset`](crate::ExecutedBlockBuilder::reset) is not called during the
    /// user's event recovery phase.
    ImplicitDrop {
        /// Start event of the block being reassembled.
        block: monad_exec_block_start,
        /// Explains why the block could not be reassembled.
        reassembly_error: ReassemblyError,
    },
}

/// Error produced by [`ExecutedBlockBuilder`](crate::ExecutedBlockBuilder) while attempting to
/// reassemble a block from execution events.
#[derive(Clone, Debug)]
pub enum ReassemblyError {
    /// A block header event was received while the current block was still being reassembled.
    ///
    /// It is guaranteed by monad-execution that all events for a given block begin with a
    /// [`monad_exec_block_start`] and end with a
    /// [`monad_exec_block_end`](crate::ffi::monad_exec_block_end), and that events for
    /// different blocks do not interleave. This implies that processing another block header before
    /// processing the previous block's block result means the block builder missed an event.
    UnterminatedBlock {
        /// The unexpected block header.
        unexpected_header: monad_exec_block_start,
    },

    /// Transaction with the given index is missing
    MissingTransaction {
        /// The missing transaction index.
        index: u64,
    },

    /// Transaction with the given index does not have the expected number
    /// of logs
    MissingTransactionLog {
        /// Missing index
        index: u64,
        /// The log count expected from the transaction receipt.
        expected_log_count: usize,
        /// The actual number of log events received.
        actual_log_count: usize,
    },
}
