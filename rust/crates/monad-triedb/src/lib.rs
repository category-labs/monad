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
    cmp::Ordering,
    ffi::CString,
    path::Path,
    ptr::{null, null_mut, NonNull},
    sync::{
        atomic::{AtomicUsize, Ordering::SeqCst},
        Arc,
    },
};

use futures::channel::oneshot::Sender;
use tracing::{debug, error};

use self::{
    ffi::{validator_data, validator_set},
    traverse::TraverseCallbackKind,
};

pub mod ffi;
mod traverse;

#[derive(Debug)]
pub struct TriedbHandle {
    db_ptr: *mut ffi::TriedbRoInner,
}

struct SenderContext {
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
struct TraverseContext {
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

/// Compute the storage page key for a 32-byte slot `key` on a page-encoded db
/// (`page_key = slot >> 7`). This is the key the storage trie is looked up by;
/// the returned page leaf is then decoded with `decode_storage_page_slot` at
/// the offset from `compute_slot_offset`. Delegates to C++ so the page geometry
/// lives in one place.
pub fn compute_page_key(key: [u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    unsafe { ffi::triedb_compute_page_key(key.as_ptr(), out.as_mut_ptr()) };
    out
}

/// Compute the slot's offset within its page for a 32-byte slot `key` (the low
/// 7 bits). This is the `offset` argument to `decode_storage_page_slot`.
pub fn compute_slot_offset(key: [u8; 32]) -> u8 {
    unsafe { ffi::triedb_compute_slot_offset(key.as_ptr()) }
}

/// Decode a page-encoded storage `leaf` (the value of a storage node on a
/// page-encoded db, looked up with the page key) and return the 32-byte value
/// of the slot at `offset` (the low 7 bits of the original slot key). Returns
/// `None` on decode error. Reuses the C++ page decode via FFI so the page
/// format lives in one place.
pub fn decode_storage_page_slot(leaf: &[u8], offset: u8) -> Option<[u8; 32]> {
    let mut out = [0u8; 32];
    let ok = unsafe {
        ffi::triedb_decode_storage_page_slot(leaf.as_ptr(), leaf.len(), offset, out.as_mut_ptr())
    };
    ok.then_some(out)
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

/// # Safety
/// This should be used only as a callback for async TrieDB calls.
///
/// This function is called by TrieDB once it processes a single read async call.
unsafe extern "C" fn read_async_callback(
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
            unsafe { ffi::triedb_finalize(value_ptr) };
            Some(value)
        }
    };

    // Send the retrieved result through the channel
    let _ = sender_context.sender.send(result);
}

// Compile-time assertion that read_async_callback signature matches triedb_async_read_callback_fn
const _: () = {
    #[allow(dead_code)]
    const fn check_signature() {
        let _: ffi::triedb_async_read_callback_fn = Some(read_async_callback);
    }
};

/// # Safety
/// This is used as a callback when traversing the transaction or receipt trie.
unsafe extern "C" fn traverse_callback(
    op_kind: ffi::triedb_async_traverse_callback,
    context: *mut std::ffi::c_void,
    key_ptr: *const u8,
    key_len: usize,
    value_ptr: *const u8,
    value_len: usize,
) {
    let context = context as *mut TraverseContext;

    let Some(op_kind) = TraverseCallbackKind::from_c(op_kind) else {
        error!(
            "traverse_callback: unexpected op_kind value: {}",
            op_kind as i32
        );
        let _ctx = unsafe { Box::from_raw(context) };
        return;
    };

    match op_kind {
        TraverseCallbackKind::FinishedEarly => {
            let ctx = unsafe { Box::from_raw(context) };
            let _ = ctx.sender.send(None);
        }
        TraverseCallbackKind::FinishedNormally => {
            let ctx = unsafe { Box::from_raw(context) };
            let data = {
                let mut lock = ctx.data.lock().expect("mutex poisoned");
                std::mem::take(&mut *lock)
            };
            let _ = ctx.sender.send(Some(data));
        }
        TraverseCallbackKind::Value => {
            let key = unsafe { std::slice::from_raw_parts(key_ptr, key_len).to_vec() };
            let value = unsafe { std::slice::from_raw_parts(value_ptr, value_len).to_vec() };

            let mut lock = unsafe { &*context }.data.lock().expect("mutex poisoned");

            lock.push(TraverseEntry { key, value });
        }
    }
}

// Compile-time assertion that traverse_callback signature matches triedb_async_traverse_callback_fn
const _: () = {
    #[allow(dead_code)]
    const fn check_signature() {
        let _: ffi::triedb_async_traverse_callback_fn = Some(traverse_callback);
    }
};

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

    /// True if the primary timeline is page-encoded (Monad state machine), in
    /// which case storage is keyed by keccak(page_key) and leaves are encoded
    /// pages (see `decode_storage_page_slot`).
    pub fn is_page_encoded(&self) -> bool {
        unsafe { ffi::triedb_is_page_encoded(self.db_ptr) }
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

        // Wrap the sender and completed_counter in a context struct
        let sender_context = Box::new(SenderContext {
            sender,
            completed_counter,
            concurrency_tracker,
        });

        unsafe {
            // Convert the struct into a raw pointer which will be sent to the callback function
            let sender_context_ptr = Box::into_raw(sender_context);

            ffi::triedb_async_read(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                Some(read_async_callback), // TrieDB read async callback
                sender_context_ptr as *mut std::ffi::c_void,
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

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Vec::default()),
            sender,
            concurrency_tracker,
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            ffi::triedb_async_traverse(
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
        if validate_nibble_key(key, key_len_nibbles, "Key").is_none() {
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
            let _result = ffi::triedb_traverse(
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
        if validate_nibble_key(min_key, min_key_len_nibbles, "Min key").is_none() {
            return;
        }
        if validate_nibble_key(max_key, max_key_len_nibbles, "Max key").is_none() {
            return;
        }

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Default::default()),
            sender,
            concurrency_tracker,
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            ffi::triedb_async_ranged_get(
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

// ── KV-DB prototype: RPC read side ──────────────────────────────────────────
// The flat-page KV store is the read authority for state and per-block data.
// This is a thin, safe wrapper over the C ABI in include/ffi.h; it deliberately
// does no interpretation of the bytes it returns (no RLP, no alloy types) so
// the decode policy stays with the caller.

/// Per-block blob categories. Some are stored as a table of independently
/// addressable entries (`Receipts`, `Transactions` and `CallFrames` indexed by
/// tx position, `Withdrawals` by withdrawal position) -- read those with
/// [`BlockGuard::table_blob`], never [`BlockGuard::block_blob`]. The rest are a
/// single blob per block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum BlobCategory {
    Receipts = 0,
    Transactions = 1,
    Header = 2,
    CallFrames = 3,
    Ommers = 4,
    Withdrawals = 5,
    TxHashes = 6,
}

impl BlobCategory {
    /// True for the categories stored as a table of per-index entries.
    pub fn is_table(self) -> bool {
        matches!(
            self,
            Self::Receipts | Self::Transactions | Self::CallFrames | Self::Withdrawals
        )
    }
}

/// An account exactly as KV stores it. No RLP is involved in either direction:
/// KV holds a fixed record, so this crosses the FFI as a packed struct.
///
/// `code_hash` is the raw hash; it equals `keccak256("")` when the account has
/// no code, which is the case the triedb RLP path reports as `None`. Mapping
/// that to an `Option` is left to the caller so this crate stays free of
/// alloy types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KvAccount {
    /// Big-endian, so this never depends on the C++ `uint256` representation.
    pub balance_be: [u8; 32],
    pub code_hash: [u8; 32],
    pub nonce: u64,
}

/// Read-only handle on the KV store. Independent of [`TriedbHandle`] -- a
/// different backend over the same device.
///
/// Execution must already be running when this is opened: it attaches exec's
/// existing hazard-pointer segment and metadata mapping. If exec restarts, this
/// handle is stale and the process must be restarted too (the segment is
/// recreated fresh, orphaning our mapping).
#[derive(Debug)]
pub struct KvHandle {
    ptr: *mut ffi::KvReaderHandle,
}

// Every read is a `pread` plus atomics: there is no shared mutable state in the
// reader besides the hazard slots, whose pool is built for concurrent readers
// (each caller takes its own slot). So the handle is safe to share across the
// RPC's worker threads.
unsafe impl Send for KvHandle {}
unsafe impl Sync for KvHandle {}

impl KvHandle {
    /// Attach the store read-only. `kvhdr_path` is the `.kvhdr` sidecar; the
    /// backing device comes from `$KVDB_DEVICE`. `None` if exec is not up or the
    /// header/metadata does not match this build.
    pub fn try_new(kvhdr_path: &Path) -> Option<Self> {
        let path = CString::new(kvhdr_path.to_str()?).ok()?;
        let mut ptr = null_mut();
        let result = unsafe { ffi::kv_open(path.as_c_str().as_ptr(), &mut ptr) };
        if result != 0 {
            debug!("kv_open failed: {}", result);
            return None;
        }
        Some(Self { ptr })
    }

    /// Pin `block` so its data cannot be reclaimed while the returned guard
    /// lives. `None` means the block is not retained (already pruned, or never
    /// existed) -- the request should be failed rather than retried in a loop.
    ///
    /// `id` is an undecided block's proposal id. `None` takes the finalized
    /// block at that height, whose block-map entry finalization made unique; an
    /// undecided height can hold several proposals, so there the id is required
    /// to say which one.
    ///
    /// Takes `&Arc<Self>` so the guard can outlive the call and be held for a
    /// whole request without borrowing the handle.
    pub fn try_protect_block(
        self: &Arc<Self>,
        block: u64,
        id: Option<&[u8; 32]>,
    ) -> Option<BlockGuard> {
        let id_ptr = id.map_or(null(), |id| id.as_ptr());
        let handle = unsafe { ffi::kv_try_protect_block(self.ptr, block, id_ptr) };
        if handle < 0 {
            return None;
        }
        Some(BlockGuard {
            kv: Arc::clone(self),
            handle,
        })
    }

    /// Code by hash. Needs no pinned block: the code store is grow-only and is
    /// never reclaimed.
    pub fn code(&self, code_hash: &[u8; 32]) -> Option<Vec<u8>> {
        let mut ptr = null();
        let mut len = 0u64;
        let found = unsafe { ffi::kv_read_code(self.ptr, code_hash.as_ptr(), &mut ptr, &mut len) };
        if !found {
            return None;
        }
        Some(take_buf(ptr, len))
    }

    /// Locate a transaction by hash: `(block, tx_index)`. Resolution only --
    /// pin the returned block before reading its data.
    ///
    /// Needs no block pin of its own. The index is a COW tree whose superseded
    /// roots are reclaimed, so the walk is protected -- by a transient hazard
    /// on the index root, taken and released inside this call.
    pub fn resolve_tx_hash(&self, hash: &[u8; 32]) -> Option<(u64, u32)> {
        let mut block = 0u64;
        let mut tx_index = 0u32;
        let found =
            unsafe { ffi::kv_resolve_tx_hash(self.ptr, hash.as_ptr(), &mut block, &mut tx_index) };
        found.then_some((block, tx_index))
    }

    /// Resolve a block hash to its number. Hazard-protected internally, as
    /// [`Self::resolve_tx_hash`] is.
    pub fn resolve_block_hash(&self, hash: &[u8; 32]) -> Option<u64> {
        let mut number = 0u64;
        let found = unsafe { ffi::kv_resolve_block_hash(self.ptr, hash.as_ptr(), &mut number) };
        found.then_some(number)
    }

    /// Finalized tip.
    pub fn finalized_block(&self) -> Option<u64> {
        cursor(unsafe { ffi::kv_finalized_block(self.ptr) })
    }

    /// Oldest block still retained; reads below this fail to pin.
    pub fn earliest_block(&self) -> Option<u64> {
        cursor(unsafe { ffi::kv_earliest_block(self.ptr) })
    }

    /// Latest proposed block (the `latest` tag). `None` until consensus stamps it.
    pub fn proposed_block(&self) -> Option<u64> {
        cursor(unsafe { ffi::kv_proposed_block(self.ptr) })
    }

    /// Latest voted block (the `safe` tag). `None` until consensus stamps it.
    pub fn voted_block(&self) -> Option<u64> {
        cursor(unsafe { ffi::kv_voted_block(self.ptr) })
    }

    /// All four tag cursors as one consistent snapshot, which is what block-tag
    /// resolution needs -- it reads finalized, voted and proposed together and
    /// must not mix two different moments. `None` means no stable `(block, id)`
    /// pair could be read, in which case the caller should keep what it had.
    pub fn tags(&self) -> Option<KvTags> {
        let mut raw = ffi::kv_tags {
            finalized: 0,
            earliest: 0,
            proposed: 0,
            proposed_id: [0; 32],
            voted: 0,
            voted_id: [0; 32],
        };
        if !unsafe { ffi::kv_read_tags(self.ptr, &mut raw) } {
            return None;
        }
        Some(KvTags {
            finalized: cursor(raw.finalized),
            earliest: cursor(raw.earliest),
            proposed: cursor(raw.proposed).map(|block| (block, raw.proposed_id)),
            voted: cursor(raw.voted).map(|block| (block, raw.voted_id)),
        })
    }
}

/// KV's block-tag cursors. The proposed and voted heads carry their block ids,
/// since a height can hold several proposals and only the id says which one is
/// canonical.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KvTags {
    pub finalized: Option<u64>,
    pub earliest: Option<u64>,
    pub proposed: Option<(u64, [u8; 32])>,
    pub voted: Option<(u64, [u8; 32])>,
}

impl Drop for KvHandle {
    fn drop(&mut self) {
        unsafe { ffi::kv_close(self.ptr) };
    }
}

/// A pinned block. All reads through it see one consistent snapshot, and that
/// snapshot cannot be reclaimed until the guard is dropped -- which happens on
/// every path out of a request, including error and cancellation.
#[derive(Debug)]
pub struct BlockGuard {
    kv: Arc<KvHandle>,
    handle: i64,
}

impl BlockGuard {
    /// `None` if the account does not exist at this block.
    pub fn account(&self, addr: &[u8; 20]) -> Option<KvAccount> {
        let mut raw = ffi::kv_account {
            balance: [0u8; 32],
            code_hash: [0u8; 32],
            nonce: 0,
        };
        let found =
            unsafe { ffi::kv_read_account(self.kv.ptr, self.handle, addr.as_ptr(), &mut raw) };
        found.then_some(KvAccount {
            balance_be: raw.balance,
            code_hash: raw.code_hash,
            nonce: raw.nonce,
        })
    }

    /// Slot value, all-zero when unset (KV stores no zero slots, so absent and
    /// zero are the same answer).
    pub fn storage(&self, addr: &[u8; 20], key: &[u8; 32]) -> [u8; 32] {
        let mut out = [0u8; 32];
        unsafe {
            ffi::kv_read_storage(
                self.kv.ptr,
                self.handle,
                addr.as_ptr(),
                key.as_ptr(),
                out.as_mut_ptr(),
            )
        };
        out
    }

    /// A whole-block blob. Panics on a table category, which must go through
    /// [`Self::table_blob`] -- reading a table as a single blob is not
    /// meaningful.
    pub fn block_blob(&self, category: BlobCategory) -> Option<Vec<u8>> {
        assert!(
            !category.is_table(),
            "{category:?} is a table; use table_blob"
        );
        let mut ptr = null();
        let mut len = 0u64;
        let found = unsafe {
            ffi::kv_read_block_blob(self.kv.ptr, self.handle, category as u32, &mut ptr, &mut len)
        };
        found.then(|| take_buf(ptr, len))
    }

    /// One entry of a table category, by its index within the block.
    pub fn table_blob(&self, category: BlobCategory, index: u32) -> Option<Vec<u8>> {
        let mut ptr = null();
        let mut len = 0u64;
        let found = unsafe {
            ffi::kv_read_tx_blob(
                self.kv.ptr,
                self.handle,
                category as u32,
                index,
                &mut ptr,
                &mut len,
            )
        };
        found.then(|| take_buf(ptr, len))
    }

    /// Whether this block carries the category at all.
    pub fn blob_present(&self, category: BlobCategory) -> bool {
        unsafe { ffi::kv_blob_present(self.kv.ptr, self.handle, category as u32) }
    }

    /// How many entries a table category holds; `None` if the category is
    /// absent or is not a table.
    pub fn table_count(&self, category: BlobCategory) -> Option<u64> {
        let n = unsafe { ffi::kv_table_count(self.kv.ptr, self.handle, category as u32) };
        (n >= 0).then_some(n as u64)
    }
}

impl Drop for BlockGuard {
    fn drop(&mut self) {
        unsafe { ffi::kv_end_block_protection(self.kv.ptr, self.handle) };
    }
}

/// Copy a buffer the C side handed us into a `Vec`, then release it. An empty
/// blob arrives as a null pointer with length 0.
fn take_buf(ptr: *const u8, len: u64) -> Vec<u8> {
    let out = if ptr.is_null() || len == 0 {
        Vec::new()
    } else {
        unsafe { std::slice::from_raw_parts(ptr, len as usize) }.to_vec()
    };
    unsafe { ffi::kv_free(ptr) };
    out
}

/// Metadata cursors use `u64::MAX` for "not set yet".
fn cursor(v: u64) -> Option<u64> {
    (v != u64::MAX).then_some(v)
}

#[cfg(test)]
mod kv_tests {
    use super::*;

    /// Cross-process smoke test of the KV read side: this test binary is a
    /// second process reading the store while execution writes it.
    ///
    /// Requires exec to be RUNNING against the same store (it owns the hazard
    /// segment and metadata this attaches to). Set `KVDB_IMAGE` to the `.kvhdr`
    /// sidecar and `KVDB_DEVICE` to the backing file/device, then run while a
    /// replay is in flight. Skipped when `KVDB_IMAGE` is unset, so a normal
    /// `cargo test` is unaffected.
    ///
    /// Correctness of the reads themselves is covered on the C++ side against
    /// triedb; what this pins down is the FFI plumbing -- pointer and lifetime
    /// handling, the packed `kv_account` layout, buffer ownership -- plus the
    /// one thing only a separate process can show: that attaching exec's shared
    /// segment from outside exec actually works.
    #[test]
    fn kv_reader_cross_process() {
        let Ok(img) = std::env::var("KVDB_IMAGE") else {
            eprintln!("KVDB_IMAGE unset; skipping");
            return;
        };

        let kv =
            Arc::new(KvHandle::try_new(Path::new(&img)).expect("kv_open (is exec running?)"));

        let finalized = kv.finalized_block().expect("finalized cursor");
        let earliest = kv.earliest_block().expect("earliest cursor");
        assert!(earliest <= finalized, "{earliest} > {finalized}");
        eprintln!("retained window: [{earliest}, {finalized}]");

        let guard = kv
            .try_protect_block(finalized, None)
            .expect("pin the finalized tip");

        // Reads must be repeatable through one pin.
        let addr = [0u8; 20];
        assert_eq!(guard.account(&addr), guard.account(&addr));
        let slot = [0u8; 32];
        assert_eq!(guard.storage(&addr, &slot), guard.storage(&addr, &slot));

        // Whole-block categories: present ones must be non-empty.
        for category in [
            BlobCategory::Header,
            BlobCategory::Ommers,
            BlobCategory::TxHashes,
        ] {
            if guard.blob_present(category) {
                let blob = guard.block_blob(category).expect("present blob reads");
                assert!(!blob.is_empty(), "{category:?} present but empty");
            }
        }

        // Per-tx tables must cover exactly the block's tx count, every entry
        // must be non-empty, and every tx hash must resolve back to its own
        // position in this block.
        let per_tx = [
            BlobCategory::Receipts,
            BlobCategory::Transactions,
            BlobCategory::CallFrames,
        ];
        if let Some(hashes) = guard.block_blob(BlobCategory::TxHashes) {
            assert_eq!(hashes.len() % 32, 0, "tx-hash blob is not a hash multiple");
            let ntx = hashes.len() / 32;
            eprintln!("block {finalized}: {ntx} txs");

            for category in per_tx {
                if guard.blob_present(category) {
                    assert_eq!(
                        guard.table_count(category),
                        Some(ntx as u64),
                        "{category:?} table does not cover every tx"
                    );
                }
            }

            for i in 0..ntx {
                let mut hash = [0u8; 32];
                hash.copy_from_slice(&hashes[i * 32..(i + 1) * 32]);
                assert_eq!(
                    kv.resolve_tx_hash(&hash),
                    Some((finalized, i as u32)),
                    "tx {i} did not resolve to its own position"
                );
                for category in per_tx {
                    if guard.blob_present(category) {
                        let blob = guard.table_blob(category, i as u32).expect("entry reads");
                        assert!(!blob.is_empty(), "{category:?}[{i}] empty");
                    }
                }
            }
        }

        // A table category must not be read as one blob.
        assert!(
            std::panic::catch_unwind(|| guard.block_blob(BlobCategory::Receipts)).is_err(),
            "reading a table as a whole blob should panic"
        );

        // Below the retained floor there is nothing to pin.
        if earliest > 0 {
            assert!(
                kv.try_protect_block(earliest - 1, None).is_none(),
                "pinned a block below the retained floor"
            );
        }

        drop(guard); // releases the pin
        eprintln!("kv_reader_cross_process ok");
    }
}
