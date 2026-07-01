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

use std::sync::{atomic::AtomicUsize, Arc, Mutex};

use futures::channel::oneshot::{Receiver, Sender};

pub(crate) use self::bindings::{
    monad_c_bytes32, triedb_async_ranged_get, triedb_async_read, triedb_async_traverse,
    triedb_close, triedb_earliest_version, triedb_finalize, triedb_free_valset,
    triedb_latest_finalized_version, triedb_latest_proposed_block_id,
    triedb_latest_proposed_version, triedb_latest_verified_version, triedb_latest_voted_block_id,
    triedb_latest_voted_version, triedb_open, triedb_poll, triedb_read, triedb_read_valset,
    triedb_traverse, CallbackContext as OpaqueCallbackContext, TriedbRoInner,
};
pub use self::bindings::{validator_data, validator_set};

#[allow(
    dead_code,
    non_camel_case_types,
    non_upper_case_globals,
    non_snake_case
)]
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

pub type AsyncReadSender = Sender<Option<Vec<u8>>>;
pub type AsyncReadReceiver = Receiver<Option<Vec<u8>>>;

pub struct AsyncReadContext {
    sender: AsyncReadSender,

    completed_counter: Arc<AtomicUsize>,
    #[allow(dead_code)]
    concurrency_tracker: Arc<()>,
}

impl AsyncReadContext {
    pub fn new(
        sender: AsyncReadSender,
        completed_counter: Arc<AtomicUsize>,
        concurrency_tracker: Arc<()>,
    ) -> Self {
        Self {
            sender,

            completed_counter,
            concurrency_tracker,
        }
    }
}

#[no_mangle]
unsafe extern "C" fn monad_rust_triedb_callback_async_read(
    ctx: *mut OpaqueCallbackContext,
    value_ptr: *const u8,
    value_len: usize,
) {
    let ctx: AsyncReadContext = *unsafe { Box::from_raw(ctx as *mut AsyncReadContext) };

    let AsyncReadContext {
        sender,

        completed_counter,
        concurrency_tracker: _,
    } = ctx;

    let value = if value_ptr.is_null() {
        None
    } else {
        Some(unsafe { std::slice::from_raw_parts(value_ptr, value_len) }.to_vec())
    };

    let _ = sender.send(value);

    completed_counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
}

const _: () = {
    let _: unsafe extern "C" fn(*mut OpaqueCallbackContext, *const u8, usize) =
        bindings::monad_rust_triedb_callback_async_read;
    let _: unsafe extern "C" fn(*mut OpaqueCallbackContext, *const u8, usize) =
        monad_rust_triedb_callback_async_read;
};

#[derive(Debug, Clone)]
pub struct TraverseEntry {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

pub type AsyncTraverseSender = Sender<Option<Vec<TraverseEntry>>>;
pub type AsyncTraverseReceiver = Receiver<Option<Vec<TraverseEntry>>>;

pub struct AsyncTraverseContext {
    data: Mutex<Vec<TraverseEntry>>,
    sender: AsyncTraverseSender,

    #[allow(dead_code)]
    concurrency_tracker: Arc<()>,
}

impl AsyncTraverseContext {
    pub fn new(sender: AsyncTraverseSender, concurrency_tracker: Arc<()>) -> Self {
        Self {
            data: Mutex::new(Vec::new()),
            sender,

            concurrency_tracker,
        }
    }
}

#[no_mangle]
unsafe extern "C" fn monad_rust_triedb_callback_traverse_value(
    ctx: *const OpaqueCallbackContext,
    key_ptr: *const u8,
    key_len: usize,
    value_ptr: *const u8,
    value_len: usize,
) {
    let AsyncTraverseContext {
        data,
        sender: _,

        concurrency_tracker: _,
    } = unsafe { &*(ctx as *const AsyncTraverseContext) };

    let key = unsafe { std::slice::from_raw_parts(key_ptr, key_len) };
    let value = unsafe { std::slice::from_raw_parts(value_ptr, value_len) };

    data.lock().expect("mutex poisoned").push(TraverseEntry {
        key: key.to_vec(),
        value: value.to_vec(),
    });
}

const _: () = {
    let _: unsafe extern "C" fn(*const OpaqueCallbackContext, *const u8, usize, *const u8, usize) =
        bindings::monad_rust_triedb_callback_traverse_value;
    let _: unsafe extern "C" fn(*const OpaqueCallbackContext, *const u8, usize, *const u8, usize) =
        monad_rust_triedb_callback_traverse_value;
};

#[no_mangle]
unsafe extern "C" fn monad_rust_triedb_callback_traverse_finished(
    ctx: *mut OpaqueCallbackContext,
    completed: bool,
) {
    let ctx: AsyncTraverseContext = *unsafe { Box::from_raw(ctx as *mut AsyncTraverseContext) };

    let AsyncTraverseContext {
        data,
        sender,

        concurrency_tracker: _,
    } = ctx;

    let data = completed.then(|| std::mem::take(data.lock().expect("mutex poisoned").as_mut()));

    let _ = sender.send(data);
}

const _: () = {
    let _: unsafe extern "C" fn(*mut OpaqueCallbackContext, bool) =
        bindings::monad_rust_triedb_callback_traverse_finished;
    let _: unsafe extern "C" fn(*mut OpaqueCallbackContext, bool) =
        monad_rust_triedb_callback_traverse_finished;
};
