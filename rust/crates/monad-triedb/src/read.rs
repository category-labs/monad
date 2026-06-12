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

use std::sync::{atomic::AtomicUsize, Arc};

use crate::{ffi, NibblesView, TriedbRoHandle};

#[inline]
fn parse_block_num(value: u64) -> Option<u64> {
    (value != u64::MAX).then_some(value)
}

#[inline]
fn parse_block_id(value: ffi::Bytes32) -> Option<[u8; 32]> {
    (value.0 != [0u8; 32]).then_some(value.0)
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

    fn read(&self, key: NibblesView<'_>, block_id: u64) -> Option<Box<[u8]>>;

    fn traverse(&mut self, key: NibblesView<'_>, block_id: u64, sender: ffi::AsyncTraverseSender);
}

pub trait TriedbAsyncRead {
    /// If `blocking`, sleeps until at least one completion is available.
    fn poll(&mut self, blocking: bool, max_completions: usize) -> usize;

    fn read_async(
        &mut self,
        key: NibblesView<'_>,
        block_id: u64,
        sender: ffi::AsyncReadSender,
        completed_counter: Arc<AtomicUsize>,
        concurrency_tracker: Arc<()>,
    );

    fn traverse_async(
        &mut self,
        key: NibblesView<'_>,
        block_id: u64,
        sender: ffi::AsyncTraverseSender,
        concurrency_tracker: Arc<()>,
    );

    fn traverse_range_async(
        &mut self,
        prefix: NibblesView<'_>,
        min: NibblesView<'_>,
        max: NibblesView<'_>,
        block_id: u64,
        sender: ffi::AsyncTraverseSender,
        concurrency_tracker: Arc<()>,
    );
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
    fn read(&self, key: NibblesView<'_>, block_id: u64) -> Option<Box<[u8]>> {
        let bytes_ptr = crate::ffi::triedb_read(&self.inner, key.bytes, key.nibble_len, block_id);

        bytes_ptr.as_ref().map(|bytes| bytes.as_slice().into())
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
    fn traverse(&mut self, key: NibblesView<'_>, block_id: u64, sender: ffi::AsyncTraverseSender) {
        let ctx = Box::into_raw(Box::new(ffi::AsyncTraverseContext::new(
            sender,
            Arc::new(()),
        ))) as *mut ffi::OpaqueCallbackContext;

        unsafe { ffi::triedb_traverse(self.inner_mut(), key.bytes, key.nibble_len, block_id, ctx) };
    }
}

impl TriedbAsyncRead for TriedbRoHandle {
    #[inline]
    fn poll(&mut self, blocking: bool, max_completions: usize) -> usize {
        ffi::triedb_poll(self.inner_mut(), blocking, max_completions)
    }

    #[inline]
    fn read_async(
        &mut self,
        key: NibblesView<'_>,
        block_id: u64,
        sender: ffi::AsyncReadSender,
        completed_counter: Arc<AtomicUsize>,
        concurrency_tracker: Arc<()>,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::AsyncReadContext::new(
            sender,
            completed_counter,
            concurrency_tracker,
        ))) as *mut ffi::OpaqueCallbackContext;

        unsafe {
            ffi::triedb_async_read(self.inner_mut(), key.bytes, key.nibble_len, block_id, ctx)
        };
    }

    #[inline]
    fn traverse_async(
        &mut self,
        key: NibblesView<'_>,
        block_id: u64,
        sender: ffi::AsyncTraverseSender,
        concurrency_tracker: Arc<()>,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::AsyncTraverseContext::new(
            sender,
            concurrency_tracker,
        ))) as *mut ffi::OpaqueCallbackContext;

        unsafe {
            ffi::triedb_async_traverse(self.inner_mut(), key.bytes, key.nibble_len, block_id, ctx)
        };
    }

    #[inline]
    fn traverse_range_async(
        &mut self,
        prefix: NibblesView<'_>,
        min: NibblesView<'_>,
        max: NibblesView<'_>,
        block_id: u64,
        sender: ffi::AsyncTraverseSender,
        concurrency_tracker: Arc<()>,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::AsyncTraverseContext::new(
            sender,
            concurrency_tracker,
        ))) as *mut ffi::OpaqueCallbackContext;

        unsafe {
            ffi::triedb_async_traverse_range(
                self.inner_mut(),
                prefix.bytes,
                prefix.nibble_len,
                min.bytes,
                min.nibble_len,
                max.bytes,
                max.nibble_len,
                block_id,
                ctx,
            );
        }
    }
}
