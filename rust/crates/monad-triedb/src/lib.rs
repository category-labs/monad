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

use std::{
    ffi::CString,
    path::Path,
    ptr::{null, null_mut, NonNull},
    sync::{atomic::AtomicUsize, Arc},
};

use futures::channel::oneshot::Sender;
use tracing::{debug, error};

pub use self::ffi::TraverseEntry;
use self::ffi::{
    validator_data, validator_set, AsyncReadContext, AsyncTraverseContext, OpaqueCallbackContext,
};

pub mod ffi;

#[derive(Debug)]
pub struct TriedbHandle {
    db_ptr: *mut ffi::TriedbRoInner,
}

/// Returns `None` if nibble length validation fails (overflow or insufficient key bytes).
fn validate_nibble_key(key: &[u8], key_len_nibbles: u8, label: &str) -> Option<()> {
    if key_len_nibbles >= u8::MAX - 1 {
        error!("{label} length nibbles exceeds maximum allowed value");
        return None;
    }
    if (key_len_nibbles as usize).div_ceil(2) > key.len() {
        error!("{label} length is insufficient for the given nibbles");
        return None;
    }
    Some(())
}

/// Converts a C `u64` sentinel value (`u64::MAX` = not found) to `Option<u64>`.
fn parse_triedb_block_num(value: u64) -> Option<u64> {
    if value == u64::MAX {
        None
    } else {
        Some(value)
    }
}

const ZERO_BYTES32: [u8; 32] = [0u8; 32];

/// Converts a C `monad_c_bytes32` sentinel value (all-zeros = not found) to `Option<[u8; 32]>`.
fn parse_triedb_block_id(value: ffi::monad_c_bytes32) -> Option<[u8; 32]> {
    if value.bytes == ZERO_BYTES32 {
        return None;
    }
    Some(value.bytes)
}

impl TriedbHandle {
    pub fn try_new(dbdir_path: &Path, node_lru_max_mem: u64) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let path_str = dbdir_path.to_str()?;
        let path = CString::new(path_str).ok()?;

        let mut db_ptr = null_mut();

        let result =
            unsafe { ffi::triedb_open(path.as_c_str().as_ptr(), &mut db_ptr, node_lru_max_mem) };

        if result != 0 {
            debug!("triedb try_new error result: {}", result);
            return None;
        }

        Some(Self { db_ptr })
    }

    pub fn read(&self, key: &[u8], key_len_nibbles: u8, block_id: u64) -> Option<Vec<u8>> {
        validate_nibble_key(key, key_len_nibbles, "Key")?;

        let mut value_ptr = null();
        let result = unsafe {
            ffi::triedb_read(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                &mut value_ptr,
                block_id,
            )
        };
        if result == -1 {
            return None;
        }

        if result == 0 {
            return Some(Vec::new());
        }

        let Ok(value_len): Result<usize, _> = result.try_into() else {
            error!("Unexpected result from triedb_read: {}", result);
            return None;
        };

        let value = unsafe { std::slice::from_raw_parts(value_ptr, value_len) }.to_vec();

        unsafe {
            ffi::triedb_finalize(value_ptr);
        }

        Some(value)
    }

    pub fn read_async(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        completed_counter: Arc<AtomicUsize>,
        sender: Sender<Option<Vec<u8>>>,
        concurrency_tracker: Arc<()>,
    ) {
        if validate_nibble_key(key, key_len_nibbles, "Key").is_none() {
            return;
        }

        let ctx = Box::new(AsyncReadContext::new(
            sender,
            completed_counter,
            concurrency_tracker,
        ));

        unsafe {
            ffi::triedb_async_read(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                Box::into_raw(ctx) as *mut OpaqueCallbackContext,
            );
        }
    }

    /// Used to pump async reads in TrieDB.
    /// if blocking is true, the thread will sleep at least until 1 completion is available to process
    /// if blocking is false, poll will return if no completion is available to process
    /// max_completions is used as a bound for maximum completions to process in this poll
    ///
    /// Returns the number of completions processed.
    /// NOTE: could call poll internally: number of calls to this functions != number of completions processed
    pub fn triedb_poll(&self, blocking: bool, max_completions: usize) -> usize {
        unsafe { ffi::triedb_poll(self.db_ptr, blocking, max_completions) }
    }

    pub fn traverse_triedb_async(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        sender: Sender<Option<Vec<TraverseEntry>>>,
        concurrency_tracker: Arc<()>,
    ) {
        if validate_nibble_key(key, key_len_nibbles, "Key").is_none() {
            return;
        }

        let ctx = Box::new(AsyncTraverseContext::new(sender, concurrency_tracker));

        unsafe {
            ffi::triedb_async_traverse(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                Box::into_raw(ctx) as *mut OpaqueCallbackContext,
            );
        };
    }

    pub fn traverse_triedb_sync(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        sender: Sender<Option<Vec<TraverseEntry>>>,
    ) {
        if validate_nibble_key(key, key_len_nibbles, "Key").is_none() {
            return;
        }

        let ctx = Box::new(AsyncTraverseContext::new(sender, Arc::new(())));

        unsafe {
            let _result = ffi::triedb_traverse(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                Box::into_raw(ctx) as *mut OpaqueCallbackContext,
            );
        };
    }

    pub fn range_get_triedb_async(
        &self,
        prefix_key: &[u8],
        prefix_key_len_nibbles: u8,
        min_key: &[u8],
        min_key_len_nibbles: u8,
        max_key: &[u8],
        max_key_len_nibbles: u8,
        block_id: u64,
        sender: Sender<Option<Vec<TraverseEntry>>>,
        concurrency_tracker: Arc<()>,
    ) {
        if validate_nibble_key(min_key, min_key_len_nibbles, "Min key").is_none() {
            return;
        }
        if validate_nibble_key(max_key, max_key_len_nibbles, "Max key").is_none() {
            return;
        }

        let ctx = Box::new(AsyncTraverseContext::new(sender, concurrency_tracker));

        unsafe {
            ffi::triedb_async_ranged_get(
                self.db_ptr,
                prefix_key.as_ptr(),
                prefix_key_len_nibbles,
                min_key.as_ptr(),
                min_key_len_nibbles,
                max_key.as_ptr(),
                max_key_len_nibbles,
                block_id,
                Box::into_raw(ctx) as *mut OpaqueCallbackContext,
            );
        };
    }

    pub fn latest_proposed_block(&self) -> Option<u64> {
        parse_triedb_block_num(unsafe { ffi::triedb_latest_proposed_version(self.db_ptr) })
    }

    /// Note that this *can* return an inconsistent blockid if concurrently written to
    pub fn latest_proposed_block_id(&self) -> Option<[u8; 32]> {
        parse_triedb_block_id(unsafe { ffi::triedb_latest_proposed_block_id(self.db_ptr) })
    }

    pub fn latest_voted_block(&self) -> Option<u64> {
        parse_triedb_block_num(unsafe { ffi::triedb_latest_voted_version(self.db_ptr) })
    }

    /// Note that this *can* return an inconsistent blockid if concurrently written to
    pub fn latest_voted_block_id(&self) -> Option<[u8; 32]> {
        parse_triedb_block_id(unsafe { ffi::triedb_latest_voted_block_id(self.db_ptr) })
    }

    pub fn latest_finalized_block(&self) -> Option<u64> {
        parse_triedb_block_num(unsafe { ffi::triedb_latest_finalized_version(self.db_ptr) })
    }

    pub fn latest_verified_block(&self) -> Option<u64> {
        parse_triedb_block_num(unsafe { ffi::triedb_latest_verified_version(self.db_ptr) })
    }

    pub fn earliest_finalized_block(&self) -> Option<u64> {
        parse_triedb_block_num(unsafe { ffi::triedb_earliest_version(self.db_ptr) })
    }

    pub fn validator_set_at_block(
        &self,
        block_num: usize,
        requested_epoch: u64,
    ) -> Option<ValidatorSet<'_>> {
        let result_ptr =
            unsafe { ffi::triedb_read_valset(self.db_ptr, block_num, requested_epoch) };

        Some(ValidatorSet {
            ptr: NonNull::new(result_ptr)?,
            _lifetime: std::marker::PhantomData,
        })
    }
}

impl Drop for TriedbHandle {
    fn drop(&mut self) {
        let result = unsafe { ffi::triedb_close(self.db_ptr) };
        if result != 0 {
            error!("Unexpected result from triedb close: {}", result);
        }
    }
}

pub struct ValidatorSet<'s> {
    ptr: NonNull<validator_set>,
    _lifetime: std::marker::PhantomData<&'s TriedbHandle>,
}

impl<'s> ValidatorSet<'s> {
    pub fn data(&self) -> &[validator_data] {
        let val_set_ptr = unsafe { self.ptr.as_ref() };

        let val_set_length: usize = val_set_ptr
            .length
            .try_into()
            .expect("validator_set length fits in usize");

        unsafe { std::slice::from_raw_parts(val_set_ptr.validators, val_set_length) }
    }
}

impl Drop for ValidatorSet<'_> {
    fn drop(&mut self) {
        unsafe { ffi::triedb_free_valset(self.ptr.as_ptr()) }
    }
}
