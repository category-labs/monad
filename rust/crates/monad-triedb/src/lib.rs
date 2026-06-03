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

use std::{path::Path, pin::Pin, sync::Arc};

use cxx::UniquePtr;

pub use self::{
    read::{NodeValue, TriedbRead},
    validator::{TriedbValSetRead, Validator, ValidatorSet},
};

pub mod ffi;
mod read;
mod validator;

pub struct TriedbRoHandle {
    inner: UniquePtr<ffi::TriedbRoInner>,
}

impl std::fmt::Debug for TriedbRoHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TriedbRoHandle").finish_non_exhaustive()
    }
}

impl TriedbRoHandle {
    fn open_impl(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
        disable_mismatching_storage_pool_check: bool,
    ) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let inner = ffi::triedb_open(
            dbdir_path.to_str()?,
            node_lru_max_mem,
            disable_mismatching_storage_pool_check,
        );

        (!inner.is_null()).then(|| Self { inner })
    }

    pub fn open(dbdir_path: &Path, node_lru_max_mem: u64) -> Option<Self> {
        Self::open_impl(dbdir_path, node_lru_max_mem, false)
    }

    pub fn open_without_mismatching_storage_pool_check(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
    ) -> Option<Self> {
        Self::open_impl(dbdir_path, node_lru_max_mem, true)
    }

    fn inner_mut(&mut self) -> Pin<&mut ffi::TriedbRoInner> {
        self.inner.as_mut().expect("TriedbRoInner is non-null")
    }

    pub fn find_async(
        &mut self,
        key: ffi::NibblesView<'_>,
        block_id: u64,
        sender: ffi::AsyncReadSender,
        concurrency_tracker: Arc<()>,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::AsyncReadContext::new(
            sender,
            concurrency_tracker,
        ))) as *mut ffi::OpaqueCallbackContext;
        unsafe { ffi::triedb_async_read(self.inner_mut(), key, block_id, ctx) };
    }

    pub fn traverse(
        &mut self,
        key: ffi::NibblesView<'_>,
        block_id: u64,
        sender: ffi::TraverseSender,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::TraverseContext::new(sender, Arc::new(()))))
            as *mut ffi::OpaqueCallbackContext;

        unsafe { ffi::triedb_traverse(self.inner_mut(), key, block_id, ctx) };
    }

    pub fn traverse_async(
        &mut self,
        key: ffi::NibblesView<'_>,
        block_id: u64,
        sender: ffi::TraverseSender,
        concurrency_tracker: Arc<()>,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::TraverseContext::new(
            sender,
            concurrency_tracker,
        ))) as *mut ffi::OpaqueCallbackContext;

        unsafe { ffi::triedb_async_traverse(self.inner_mut(), key, block_id, ctx) };
    }

    pub fn traverse_range(
        &mut self,
        prefix: ffi::NibblesView<'_>,
        min: ffi::NibblesView<'_>,
        max: ffi::NibblesView<'_>,
        block_id: u64,
        sender: ffi::TraverseSender,
        concurrency_tracker: Arc<()>,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::TraverseContext::new(
            sender,
            concurrency_tracker,
        ))) as *mut ffi::OpaqueCallbackContext;

        unsafe {
            ffi::triedb_async_ranged_get(self.inner_mut(), prefix, min, max, block_id, ctx);
        }
    }

    /// If `blocking`, sleeps until at least one completion is available.
    pub fn poll(&mut self, blocking: bool, max_completions: usize) -> usize {
        ffi::triedb_poll(self.inner_mut(), blocking, max_completions)
    }
}
