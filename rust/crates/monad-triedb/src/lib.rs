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

use std::{
    cmp::Ordering,
    ffi::CString,
    path::Path,
    ptr::{null, null_mut, slice_from_raw_parts},
    sync::{
        atomic::{AtomicUsize, Ordering::SeqCst},
        Arc,
    },
};

use futures::channel::oneshot::Sender;
use tracing::{debug, error};

use crate::bindings::{validator_data, validator_set};

#[allow(dead_code, non_camel_case_types, non_upper_case_globals)]
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/triedb.rs"));
}

#[derive(Debug)]
pub struct TriedbHandle {
    db_ptr: *mut bindings::triedb,
}

pub struct SenderContext {
    sender: Sender<Option<Vec<u8>>>,
    completed_counter: Arc<AtomicUsize>,

    // The strong count of this dummy Arc<> reflects the total number of currently executing
    // (concurrent) requests, and this number is used by upstream code to maintain request
    // backpressure.  When this request completes, this Arc<> is implicitly dropped, which
    // causes the concurrent request count to be decremented.
    #[allow(dead_code)]
    concurrency_tracker: Arc<()>,
}

#[derive(Debug)]
pub struct TraverseContext {
    // values in traversal order
    data: std::sync::Mutex<Vec<TraverseEntry>>,
    sender: Sender<Option<Vec<TraverseEntry>>>,

    // The strong count of this dummy Arc<> reflects the total number of currently executing
    // (concurrent) requests, and this number is used by upstream code to maintain request
    // backpressure.  When this request completes, this Arc<> is implicitly dropped, which
    // causes the concurrent request count to be decremented.
    #[allow(dead_code)]
    concurrency_tracker: Arc<()>,
}

#[derive(Debug)]
pub struct TraverseEntry {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

/// # Safety
/// This should be used only as a callback for async TrieDB calls
///
/// This function is called by TrieDB once it proceses a single read async call
pub unsafe extern "C" fn read_async_callback(
    value_ptr: *const u8,
    value_len: i32,
    sender_context: *mut std::ffi::c_void,
) {
    // Unwrap the sender context struct
    let sender_context = unsafe { Box::from_raw(sender_context as *mut SenderContext) };
    // Increment the completed counter
    sender_context.completed_counter.fetch_add(1, SeqCst);

    let result = match value_len.cmp(&0) {
        Ordering::Less => None,
        Ordering::Equal => Some(Vec::new()),
        Ordering::Greater => {
            let value =
                unsafe { std::slice::from_raw_parts(value_ptr, value_len as usize).to_vec() };
            unsafe { bindings::triedb_finalize(value_ptr) };
            Some(value)
        }
    };

    // Send the retrieved result through the channel
    let _ = sender_context.sender.send(result);
}

/// # Safety
/// This is used as a callback when traversing the transaction or receipt trie
pub unsafe extern "C" fn traverse_callback(
    op_kind: bindings::triedb_async_traverse_callback,
    context: *mut std::ffi::c_void,
    key_ptr: *const u8,
    key_len: usize,
    value_ptr: *const u8,
    value_len: usize,
) {
    let traverse_context = unsafe { Box::from_raw(context as *mut TraverseContext) };

    if op_kind
        == bindings::triedb_async_traverse_callback_triedb_async_traverse_callback_finished_early
    {
        let _ = traverse_context.sender.send(None);
        // traverse_context is freed here, because we don't call Box::into_raw
        return;
    }
    if op_kind
        == bindings::triedb_async_traverse_callback_triedb_async_traverse_callback_finished_normally
    {
        // completed
        let mut lock = traverse_context.data.lock().expect("mutex poisoned");
        let _ = traverse_context
            .sender
            .send(Some(std::mem::take(&mut *lock)));
        // traverse_context is freed here, because we don't call Box::into_raw
        return;
    }
    assert_eq!(
        op_kind,
        bindings::triedb_async_traverse_callback_triedb_async_traverse_callback_value
    );

    let key = unsafe {
        let key = std::slice::from_raw_parts(key_ptr, key_len).to_vec();
        key
    };

    let value = unsafe {
        let value = std::slice::from_raw_parts(value_ptr, value_len).to_vec();
        value
    };

    {
        let mut lock = traverse_context.data.lock().expect("mutex poisoned");
        lock.push(TraverseEntry { key, value });
    }

    // prevent Box<TraverseContext> from dropping
    let _ = Box::into_raw(traverse_context);
}

impl TriedbHandle {
    pub fn try_new(dbdir_path: &Path, node_lru_max_mem: u64) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let path = CString::new(dbdir_path.to_str().expect("invalid path"))
            .expect("failed to create CString");

        let mut db_ptr = null_mut();

        let result = unsafe {
            bindings::triedb_open(path.as_c_str().as_ptr(), &mut db_ptr, node_lru_max_mem)
        };

        if result != 0 {
            debug!("triedb try_new error result: {}", result);
            return None;
        }

        Some(Self { db_ptr })
    }

    pub fn read(&self, key: &[u8], key_len_nibbles: u8, block_id: u64) -> Option<Vec<u8>> {
        let mut value_ptr = null();
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            error!("Key length nibbles exceeds maximum allowed value");
            return None;
        }
        if (key_len_nibbles as usize).div_ceil(2) > key.len() {
            error!("Key length is insufficient for the given nibbles");
            return None;
        }

        let result = unsafe {
            bindings::triedb_read(
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

        // check that there's no unexpected error
        if result <= 0 {
            error!("Unexpected result from triedb_read: {}", result);
            return None;
        }

        let value_len = result.try_into().unwrap();
        let value = unsafe {
            let value = std::slice::from_raw_parts(value_ptr, value_len).to_vec();
            bindings::triedb_finalize(value_ptr);
            value
        };

        Some(value)
    }

    /// This is used to make an async read call to TrieDB.
    /// It creates a oneshot channel and Boxes its sender and the completed_counter
    /// into a context struct and passes it to TrieDB. When TrieDB completes processing
    /// the call, it will call the `read_async_callback` which will unwrap the context
    /// struct, increment the completed_counter, and send the retrieved TrieDB value
    /// through the channel.
    /// The user needs to poll TrieDB using the `triedb_poll` function to pump the async
    /// reads and wait on the returned receiver for the value.
    /// NOTE: the returned receiver must be resolved before key is dropped
    pub fn read_async(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        completed_counter: Arc<AtomicUsize>,
        sender: Sender<Option<Vec<u8>>>,
        concurrency_tracker: Arc<()>,
    ) {
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            error!("Key length nibbles exceeds maximum allowed value");
            return;
        }
        if (key_len_nibbles as usize).div_ceil(2) > key.len() {
            error!("Key length is insufficient for the given nibbles");
            return;
        }

        // Wrap the sender and completed_counter in a context struct
        let sender_context = Box::new(SenderContext {
            sender,
            completed_counter,
            concurrency_tracker,
        });

        unsafe {
            // Convert the struct into a raw pointer which will be sent to the callback function
            let sender_context_ptr = Box::into_raw(sender_context);

            bindings::triedb_async_read(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                Some(read_async_callback), // TrieDB read async callback
                sender_context_ptr as *mut std::ffi::c_void,
            );
        }
    }

    /// Used to pump async reads in TrieDB
    /// if blocking is true, the thread will sleep at least until 1 completion is available to process
    /// if blocking is false, poll will return if no completion is available to process
    /// max_completions is used as a bound for maximum completions to process in this poll
    ///
    /// Returns the number of completions processed
    /// NOTE: could call poll internally: number of calls to this functions != number of completions processed
    pub fn triedb_poll(&self, blocking: bool, max_completions: usize) -> usize {
        unsafe { bindings::triedb_poll(self.db_ptr, blocking, max_completions) }
    }

    pub fn traverse_triedb_async(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        sender: Sender<Option<Vec<TraverseEntry>>>,
        concurrency_tracker: Arc<()>,
    ) {
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            error!("Key length nibbles exceeds maximum allowed value");
            return;
        }
        if (key_len_nibbles as usize).div_ceil(2) > key.len() {
            error!("Key length is insufficient for the given nibbles");
            return;
        }

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Default::default()),
            sender,
            concurrency_tracker,
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            bindings::triedb_async_traverse(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                context,
                Some(traverse_callback),
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
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            error!("Key length nibbles exceeds maximum allowed value");
            return;
        }
        if (key_len_nibbles as usize).div_ceil(2) > key.len() {
            error!("Key length is insufficient for the given nibbles");
            return;
        }

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Default::default()),
            sender,
            concurrency_tracker: Arc::new(()),
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            // sync result is already handled by traverse_callback
            let _result = bindings::triedb_traverse(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                context,
                Some(traverse_callback),
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
        // make sure doesn't overflow
        if min_key_len_nibbles >= u8::MAX - 1 {
            error!("Min key length nibbles exceeds maximum allowed value");
            return;
        }
        if (min_key_len_nibbles as usize).div_ceil(2) > min_key.len() {
            error!("Min key length is insufficient for the given nibbles");
            return;
        }
        if max_key_len_nibbles >= u8::MAX - 1 {
            error!("Max key length nibbles exceeds maximum allowed value");
            return;
        }
        if (max_key_len_nibbles as usize).div_ceil(2) > max_key.len() {
            error!("Max key length is insufficient for the given nibbles");
            return;
        }

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Default::default()),
            sender,
            concurrency_tracker,
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            bindings::triedb_async_ranged_get(
                self.db_ptr,
                prefix_key.as_ptr(),
                prefix_key_len_nibbles,
                min_key.as_ptr(),
                min_key_len_nibbles,
                max_key.as_ptr(),
                max_key_len_nibbles,
                block_id,
                context,
                Some(traverse_callback),
            );
        };
    }

    pub fn latest_proposed_block(&self) -> Option<u64> {
        let maybe_latest_proposed_block =
            unsafe { bindings::triedb_latest_proposed_block(self.db_ptr) };
        if maybe_latest_proposed_block == u64::MAX {
            None
        } else {
            Some(maybe_latest_proposed_block)
        }
    }

    /// Note that this *can* return an inconsistent blockid if concurrently written to
    pub fn latest_proposed_block_id(&self) -> Option<[u8; 32]> {
        let maybe_latest_proposed_block_id =
            unsafe { bindings::triedb_latest_proposed_block_id(self.db_ptr) };
        if maybe_latest_proposed_block_id.is_null() {
            None
        } else {
            let id: [u8; 32] = unsafe {
                std::slice::from_raw_parts(maybe_latest_proposed_block_id, 32)
                    .try_into()
                    .unwrap()
            };
            unsafe { bindings::triedb_finalize(maybe_latest_proposed_block_id) };
            Some(id)
        }
    }

    pub fn latest_voted_block(&self) -> Option<u64> {
        let maybe_latest_voted_block = unsafe { bindings::triedb_latest_voted_block(self.db_ptr) };
        if maybe_latest_voted_block == u64::MAX {
            None
        } else {
            Some(maybe_latest_voted_block)
        }
    }

    /// Note that this *can* return an inconsistent blockid if concurrently written to
    pub fn latest_voted_block_id(&self) -> Option<[u8; 32]> {
        let maybe_latest_voted_block_id =
            unsafe { bindings::triedb_latest_voted_block_id(self.db_ptr) };
        if maybe_latest_voted_block_id.is_null() {
            None
        } else {
            let id: [u8; 32] = unsafe {
                std::slice::from_raw_parts(maybe_latest_voted_block_id, 32)
                    .try_into()
                    .unwrap()
            };
            unsafe { bindings::triedb_finalize(maybe_latest_voted_block_id) };
            Some(id)
        }
    }

    pub fn latest_finalized_block(&self) -> Option<u64> {
        let maybe_latest_finalized_block =
            unsafe { bindings::triedb_latest_finalized_block(self.db_ptr) };
        if maybe_latest_finalized_block == u64::MAX {
            None
        } else {
            Some(maybe_latest_finalized_block)
        }
    }

    pub fn latest_verified_block(&self) -> Option<u64> {
        let maybe_latest_verified_block =
            unsafe { bindings::triedb_latest_verified_block(self.db_ptr) };
        if maybe_latest_verified_block == u64::MAX {
            None
        } else {
            Some(maybe_latest_verified_block)
        }
    }

    pub fn earliest_finalized_block(&self) -> Option<u64> {
        let maybe_earliest_finalized_block =
            unsafe { bindings::triedb_earliest_finalized_block(self.db_ptr) };
        if maybe_earliest_finalized_block == u64::MAX {
            None
        } else {
            Some(maybe_earliest_finalized_block)
        }
    }

    pub fn validator_set_at_block(
        &self,
        block_num: usize,
        requested_epoch: u64,
    ) -> ValidatorSet<'_> {
        let result_ptr = unsafe { bindings::read_valset(self.db_ptr, block_num, requested_epoch) };

        // assert read valset didn't fail
        assert!(!result_ptr.is_null());

        ValidatorSet {
            validator_set: unsafe { &mut *result_ptr },
        }
    }
}

impl Drop for TriedbHandle {
    fn drop(&mut self) {
        let result = unsafe { bindings::triedb_close(self.db_ptr) };
        if result != 0 {
            error!("Unexpected result from triedb close: {}", result);
        }
    }
}

pub struct ValidatorSet<'s> {
    validator_set: &'s mut validator_set,
}

impl<'s> ValidatorSet<'s> {
    pub fn data(&self) -> &[validator_data] {
        let val_set_ptr = self.validator_set.validators;

        let val_set_length: usize = self
            .validator_set
            .length
            .try_into()
            .expect("val_set_length doesn't fit in usize");

        unsafe {
            slice_from_raw_parts(val_set_ptr, val_set_length)
                .as_ref()
                .unwrap()
        }
    }
}

impl Drop for ValidatorSet<'_> {
    fn drop(&mut self) {
        unsafe { bindings::free_valset(self.validator_set) }
    }
}
