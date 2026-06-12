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

pub use self::bridge::Validator;
pub(crate) use self::bridge::{
    triedb_async_read, triedb_async_traverse, triedb_async_traverse_range, triedb_earliest_version,
    triedb_latest_finalized_version, triedb_latest_proposed_block_id,
    triedb_latest_proposed_version, triedb_latest_verified_version, triedb_latest_version,
    triedb_latest_voted_block_id, triedb_latest_voted_version, triedb_open, triedb_poll,
    triedb_read, triedb_read_valset, triedb_traverse, validator_bls_pubkey, validator_secp_pubkey,
    validator_stake, TriedbRoInner,
};

#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Bytes32(pub [u8; 32]);

unsafe impl cxx::ExternType for Bytes32 {
    type Id = cxx::type_id!("monad::bytes32_t");
    type Kind = cxx::kind::Trivial;
}

#[repr(C)]
pub struct OpaqueCallbackContext(());

// This allows `cxx` to resolve `CallbackContext` to `OpaqueCallbackContext` without renaming it
// across the bridge.
use OpaqueCallbackContext as CallbackContext;

#[cxx::bridge(namespace = "monad::rust")]
mod bridge {
    #[namespace = "monad"]
    unsafe extern "C++" {
        include!("monad-triedb/include/ffi.h");

        type bytes32_t = crate::ffi::Bytes32;
    }

    #[namespace = "monad::staking"]
    unsafe extern "C++" {
        include!("monad-triedb/include/ffi.h");

        type Validator;

        fn validator_secp_pubkey(validator: &Validator) -> [u8; 33];
        fn validator_bls_pubkey(validator: &Validator) -> [u8; 48];
        fn validator_stake(validator: &Validator) -> [u8; 32];
    }

    unsafe extern "C++" {
        include!("monad-triedb/include/ffi.h");

        type TriedbRoInner;

        fn triedb_open(dbdirpath: &str, node_lru_max_mem: u64) -> UniquePtr<TriedbRoInner>;

        fn triedb_poll(inner: Pin<&mut TriedbRoInner>, blocking: bool, count: usize) -> usize;

        fn triedb_latest_proposed_version(inner: &TriedbRoInner) -> u64;
        fn triedb_latest_voted_version(inner: &TriedbRoInner) -> u64;
        fn triedb_latest_finalized_version(inner: &TriedbRoInner) -> u64;
        fn triedb_latest_verified_version(inner: &TriedbRoInner) -> u64;

        fn triedb_earliest_version(inner: &TriedbRoInner) -> u64;
        fn triedb_latest_version(inner: &TriedbRoInner) -> u64;

        /// Returns all-zeros if no proposed block is recorded.
        fn triedb_latest_proposed_block_id(inner: &TriedbRoInner) -> bytes32_t;

        /// Returns all-zeros if no voted block is recorded.
        fn triedb_latest_voted_block_id(inner: &TriedbRoInner) -> bytes32_t;

        fn triedb_read(
            inner: &TriedbRoInner,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
        ) -> UniquePtr<CxxVector<u8>>;

        unsafe fn triedb_async_read(
            inner: Pin<&mut TriedbRoInner>,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut CallbackContext,
        );

        unsafe fn triedb_traverse(
            inner: Pin<&mut TriedbRoInner>,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut CallbackContext,
        );

        unsafe fn triedb_async_traverse(
            inner: Pin<&mut TriedbRoInner>,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut CallbackContext,
        );

        unsafe fn triedb_async_traverse_range(
            inner: Pin<&mut TriedbRoInner>,
            prefix_key: &[u8],
            prefix_key_len_nibbles: u8,
            min_key: &[u8],
            min_key_len_nibbles: u8,
            max_key: &[u8],
            max_key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut CallbackContext,
        );

        fn triedb_read_valset(
            inner: Pin<&mut TriedbRoInner>,
            block_num: usize,
            requested_epoch: u64,
        ) -> UniquePtr<CxxVector<Validator>>;
    }

    // Generates VectorElement for Validator so CxxVector<Validator> is usable.
    impl CxxVector<Validator> {}

    #[namespace = "monad::rust::ffi"]
    extern "Rust" {
        type CallbackContext;

        /// This function is responsible for deallocating `ctx`.
        unsafe fn callback_async_read(ctx: *mut CallbackContext, value: &[u8], found: bool);

        unsafe fn callback_traverse_value(ctx: *const CallbackContext, key: &[u8], value: &[u8]);

        /// This function is responsible for deallocating `ctx`.
        unsafe fn callback_traverse_finished(ctx: *mut CallbackContext, completed: bool);
    }
}

pub type AsyncReadSender = Sender<Option<Box<[u8]>>>;
pub type AsyncReadReceiver = Receiver<Option<Box<[u8]>>>;

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

unsafe fn callback_async_read(ctx: *mut OpaqueCallbackContext, value: &[u8], found: bool) {
    let ctx: AsyncReadContext = *unsafe { Box::from_raw(ctx as *mut AsyncReadContext) };

    let AsyncReadContext {
        sender,

        completed_counter,
        concurrency_tracker: _,
    } = ctx;

    let _ = sender.send(found.then(|| value.into()));

    completed_counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
}

#[derive(Debug, Clone)]
pub struct TraverseEntry {
    pub key: Box<[u8]>,
    pub value: Box<[u8]>,
}

pub type AsyncTraverseSender = Sender<Option<Box<[TraverseEntry]>>>;
pub type AsyncTraverseReceiver = Receiver<Option<Box<[TraverseEntry]>>>;

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

unsafe fn callback_traverse_value(ctx: *const OpaqueCallbackContext, key: &[u8], value: &[u8]) {
    let AsyncTraverseContext {
        data,
        sender: _,

        concurrency_tracker: _,
    } = unsafe { &*(ctx as *const AsyncTraverseContext) };

    data.lock().unwrap().push(TraverseEntry {
        key: key.into(),
        value: value.into(),
    });
}

unsafe fn callback_traverse_finished(ctx: *mut OpaqueCallbackContext, completed: bool) {
    let ctx: AsyncTraverseContext = *unsafe { Box::from_raw(ctx as *mut AsyncTraverseContext) };

    let AsyncTraverseContext {
        data,
        sender,

        concurrency_tracker: _,
    } = ctx;

    let data = if completed {
        Some(Vec::into_boxed_slice(std::mem::take(
            data.lock().unwrap().as_mut(),
        )))
    } else {
        None
    };

    let _ = sender.send(data);
}
