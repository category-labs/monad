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
    ffi::{NibblesView, UpsertEntry},
    read::{NodeValue, TriedbRead},
    validator::{TriedbValSetRead, Validator, ValidatorSet},
};

pub mod ffi;
mod read;
mod validator;

pub struct TriedbRoHandle {
    inner: UniquePtr<ffi::TriedbRoInner>,
}

pub struct TriedbRwHandle {
    inner: UniquePtr<ffi::TriedbRwInner>,
}

impl std::fmt::Debug for TriedbRoHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TriedbRoHandle").finish_non_exhaustive()
    }
}

impl std::fmt::Debug for TriedbRwHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TriedbRwHandle").finish_non_exhaustive()
    }
}

impl TriedbRoHandle {
    fn open_impl(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
        disable_mismatching_storage_pool_check: bool,
    ) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let inner = ffi::triedb_open_ro(
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
        unsafe { ffi::triedb_ro_async_read(self.inner_mut(), key, block_id, ctx) };
    }

    pub fn traverse(
        &mut self,
        key: ffi::NibblesView<'_>,
        block_id: u64,
        sender: ffi::TraverseSender,
    ) {
        let ctx = Box::into_raw(Box::new(ffi::TraverseContext::new(sender, Arc::new(()))))
            as *mut ffi::OpaqueCallbackContext;

        unsafe { ffi::triedb_ro_traverse(self.inner_mut(), key, block_id, ctx) };
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

        unsafe { ffi::triedb_ro_async_traverse(self.inner_mut(), key, block_id, ctx) };
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
            ffi::triedb_ro_async_ranged_get(self.inner_mut(), prefix, min, max, block_id, ctx);
        }
    }

    /// If `blocking`, sleeps until at least one completion is available.
    pub fn poll(&mut self, blocking: bool, max_completions: usize) -> usize {
        ffi::triedb_ro_poll(self.inner_mut(), blocking, max_completions)
    }
}

impl TriedbRwHandle {
    pub fn create_memory(file_size_gb: i64, compaction: bool) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let inner = ffi::triedb_open_rw_memory(file_size_gb, compaction);

        (!inner.is_null()).then(|| Self { inner })
    }

    fn new_impl(
        dbdir_path: &Path,
        append: bool,
        file_size_gb: i64,
        compaction: bool,
    ) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let inner = ffi::triedb_open_rw(dbdir_path.to_str()?, append, file_size_gb, compaction);

        (!inner.is_null()).then(|| Self { inner })
    }

    pub fn create(dbdir_path: &Path, file_size_gb: i64, compaction: bool) -> Option<Self> {
        Self::new_impl(dbdir_path, false, file_size_gb, compaction)
    }

    pub fn open(dbdir_path: &Path, file_size_gb: i64, compaction: bool) -> Option<Self> {
        Self::new_impl(dbdir_path, true, file_size_gb, compaction)
    }

    fn inner_mut(&mut self) -> Pin<&mut ffi::TriedbRwInner> {
        self.inner.as_mut().expect("TriedbRwInner is non-null")
    }

    pub fn upsert(&mut self, updates: &[UpsertEntry], block_id: u64) {
        ffi::triedb_rw_upsert(self.inner_mut(), updates, block_id);
    }

    pub fn clear_root(&mut self) {
        ffi::triedb_rw_clear_root(self.inner_mut());
    }

    pub fn load_root(&mut self, version: u64) -> bool {
        ffi::triedb_rw_load_root(self.inner_mut(), version)
    }

    pub fn update_finalized_version(&mut self, version: u64) {
        ffi::triedb_rw_update_finalized_version(self.inner_mut(), version);
    }

    pub fn update_voted_metadata(&mut self, version: u64, block_id: [u8; 32]) {
        ffi::triedb_rw_update_voted_metadata(self.inner_mut(), version, &ffi::Bytes32(block_id));
    }

    pub fn update_proposed_metadata(&mut self, version: u64, block_id: [u8; 32]) {
        ffi::triedb_rw_update_proposed_metadata(self.inner_mut(), version, &ffi::Bytes32(block_id));
    }
}
