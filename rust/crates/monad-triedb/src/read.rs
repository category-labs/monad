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

use cxx::UniquePtr;

use crate::{ffi, NibblesView, TriedbRoHandle};

/// A value read from the triedb, holding a cursor that pins the underlying
/// node in the cache. The byte view is valid as long as the `NodeValue` is
/// alive.
pub struct NodeValue {
    cursor: UniquePtr<ffi::NodeCursor>,
}

impl NodeValue {
    fn new(cursor: UniquePtr<ffi::NodeCursor>) -> Option<Self> {
        (!cursor.is_null()).then_some(Self { cursor })
    }

    pub fn as_bytes(&self) -> &[u8] {
        ffi::node_cursor_as_bytes(self.cursor.as_ref().expect("NodeValue is non-null"))
    }

    pub fn into_boxed_slice(self) -> Box<[u8]> {
        self.as_bytes().into()
    }
}

impl std::fmt::Debug for NodeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeValue")
            .field("bytes", &self.as_bytes())
            .finish()
    }
}

pub trait TriedbRead {
    fn latest_proposed_block(&self) -> Option<u64>;
    fn latest_voted_block(&self) -> Option<u64>;
    fn latest_finalized_block(&self) -> Option<u64>;
    fn latest_verified_block(&self) -> Option<u64>;

    fn earliest_finalized_block(&self) -> Option<u64>;
    fn latest_version(&self) -> Option<u64>;

    /// May return an inconsistent id under concurrent writes.
    fn latest_proposed_block_id(&self) -> Option<[u8; 32]>;

    /// May return an inconsistent id under concurrent writes.
    fn latest_voted_block_id(&self) -> Option<[u8; 32]>;

    fn read(&self, key: NibblesView<'_>, block_id: u64) -> Option<NodeValue>;
}

#[inline]
fn parse_block_num(value: u64) -> Option<u64> {
    (value != u64::MAX).then_some(value)
}

#[inline]
fn parse_block_id(value: ffi::Bytes32) -> Option<[u8; 32]> {
    (value.0 != [0u8; 32]).then_some(value.0)
}

impl TriedbRead for TriedbRoHandle {
    #[inline]
    fn latest_proposed_block(&self) -> Option<u64> {
        parse_block_num(crate::ffi::triedb_latest_proposed_version(&self.inner))
    }

    #[inline]
    fn latest_voted_block(&self) -> Option<u64> {
        parse_block_num(crate::ffi::triedb_latest_voted_version(&self.inner))
    }

    #[inline]
    fn latest_finalized_block(&self) -> Option<u64> {
        parse_block_num(crate::ffi::triedb_latest_finalized_version(&self.inner))
    }

    #[inline]
    fn latest_verified_block(&self) -> Option<u64> {
        parse_block_num(crate::ffi::triedb_latest_verified_version(&self.inner))
    }

    #[inline]
    fn earliest_finalized_block(&self) -> Option<u64> {
        parse_block_num(crate::ffi::triedb_earliest_version(&self.inner))
    }

    #[inline]
    fn latest_version(&self) -> Option<u64> {
        parse_block_num(crate::ffi::triedb_latest_version(&self.inner))
    }

    #[inline]
    fn latest_proposed_block_id(&self) -> Option<[u8; 32]> {
        parse_block_id(crate::ffi::triedb_latest_proposed_block_id(&self.inner))
    }

    #[inline]
    fn latest_voted_block_id(&self) -> Option<[u8; 32]> {
        parse_block_id(crate::ffi::triedb_latest_voted_block_id(&self.inner))
    }

    #[inline]
    fn read(&self, key: NibblesView<'_>, block_id: u64) -> Option<NodeValue> {
        NodeValue::new(crate::ffi::triedb_read(
            &self.inner,
            key.bytes,
            key.nibble_len,
            block_id,
        ))
    }
}
