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

use crate::ffi::{
    triedb_async_traverse_callback,
    triedb_async_traverse_callback_triedb_async_traverse_callback_finished_early,
    triedb_async_traverse_callback_triedb_async_traverse_callback_finished_normally,
    triedb_async_traverse_callback_triedb_async_traverse_callback_value,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TraverseCallbackKind {
    /// A key-value pair was encountered during traversal
    Value,
    /// Traversal completed normally
    FinishedNormally,
    /// Traversal finished early (error or early exit)
    FinishedEarly,
}

impl TraverseCallbackKind {
    pub(crate) fn from_c(kind: triedb_async_traverse_callback) -> Option<Self> {
        #[allow(non_upper_case_globals)]
        match kind {
            triedb_async_traverse_callback_triedb_async_traverse_callback_value => {
                Some(TraverseCallbackKind::Value)
            }
            triedb_async_traverse_callback_triedb_async_traverse_callback_finished_normally => {
                Some(TraverseCallbackKind::FinishedNormally)
            }
            triedb_async_traverse_callback_triedb_async_traverse_callback_finished_early => {
                Some(TraverseCallbackKind::FinishedEarly)
            }
            _ => None,
        }
    }
}
