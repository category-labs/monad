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

/// Dual-DB migration phase read from the triedb metadata, mirroring what
/// `monad-mpt` reports. Fully determines each timeline's encoding, so
/// readers derive both from it. Cheap and safe on a read-only handle while
/// execution is writing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum MigrationPhase {
    /// Primary ethereum, no secondary timeline: migration not started.
    Legacy = 0,
    /// Primary ethereum, page secondary backfilling: migration in progress.
    DualTimeline = 1,
    /// Primary monad, no secondary: migration complete.
    PageEncoded = 2,
    /// Primary monad, slot secondary kept as pre-cutoff history (archive
    /// nodes after the offline promote).
    Promoted = 3,
}

impl MigrationPhase {
    fn from_code(code: u8) -> Self {
        match code {
            1 => Self::DualTimeline,
            2 => Self::PageEncoded,
            3 => Self::Promoted,
            _ => Self::Legacy,
        }
    }
}

/// Storage-pool disk capacity and usage in bytes. Zeros for in-memory /
/// not-on-disk Dbs. Safe on a read-only handle while execution is writing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StorageStats {
    pub disk_capacity_bytes: u64,
    pub disk_used_bytes: u64,
}

/// Lifetime totals of the trie updates performed by the process writing the
/// db, read from the statistics sidecar that process publishes. They restart
/// at zero when that process does. `fast` and `slow` name the two node rings.
/// No `Default`: substituting zeros for a lost sample reads as a counter reset
/// to anything computing a rate over these.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct UpdateStats {
    pub nodes_created_or_updated: u64,
    pub nreads_compaction: u64,
    pub nreads_before_compact_offset_fast: u64,
    pub nreads_before_compact_offset_slow: u64,
    pub nreads_after_compact_offset_fast: u64,
    pub nreads_after_compact_offset_slow: u64,
    pub bytes_read_before_compact_offset_fast: u64,
    pub bytes_read_before_compact_offset_slow: u64,
    pub bytes_read_after_compact_offset_fast: u64,
    pub bytes_read_after_compact_offset_slow: u64,
    pub compacted_nodes_in_fast: u64,
    pub compacted_nodes_in_slow: u64,
    pub nodes_copied_fast_to_fast_for_fast: u64,
    pub nodes_copied_fast_to_fast_for_slow: u64,
    pub nodes_copied_slow_to_fast_for_slow: u64,
    pub compacted_bytes_in_fast: u64,
    pub compacted_bytes_in_slow: u64,
    pub bytes_copied_slow_to_fast_for_slow: u64,
    pub nodes_updated_expire: u64,
    pub nreads_expire: u64,
}

// The only place a counter added upstream would otherwise be dropped in
// silence: every C++ layer fails to compile or trips a static_assert, while
// this struct and the copy below would keep building unchanged.
const _: () =
    assert!(std::mem::size_of::<ffi::triedb_update_stats>() == std::mem::size_of::<UpdateStats>());

/// Reader for the statistics sidecar published by a writing db (see the
/// execution binary's `--db-stats-file`). Independent of [`TriedbHandle`]:
/// the sidecar is a separate path, is absent unless the writer was
/// configured with one, and carries counters no read-only db handle can see.
#[derive(Debug)]
pub struct TriedbStatsReader {
    ptr: *mut ffi::TriedbStatsReader,
}

impl TriedbStatsReader {
    /// None if the sidecar is absent or is not one this build understands.
    pub fn try_new(path: &Path) -> Option<Self> {
        let Some(path_str) = path.to_str() else {
            error!("triedb stats sidecar path is not utf-8: {}", path.display());
            return None;
        };
        let Ok(c_path) = CString::new(path_str) else {
            error!(
                "triedb stats sidecar path contains a nul: {}",
                path.display()
            );
            return None;
        };

        let mut ptr = null_mut();
        let result = unsafe { ffi::triedb_stats_open(c_path.as_c_str().as_ptr(), &mut ptr) };
        if result != 0 {
            debug!(
                "triedb stats sidecar {} unavailable: {}",
                path.display(),
                result
            );
            return None;
        }

        Some(Self { ptr })
    }

    /// None if the writing db predates the counters, or if it kept
    /// republishing them for the whole retry budget. All-zero is a valid
    /// reading from a writer that has not upserted yet.
    pub fn update_stats(&self) -> Option<UpdateStats> {
        // Plain C struct of u64 counters: zeroed is a valid value, and the
        // reader overwrites all of it or none of it.
        let mut out: ffi::triedb_update_stats = unsafe { std::mem::zeroed() };
        if !unsafe { ffi::triedb_update_stats_read(self.ptr, &mut out) } {
            return None;
        }

        Some(UpdateStats {
            nodes_created_or_updated: out.nodes_created_or_updated,
            nreads_compaction: out.nreads_compaction,
            nreads_before_compact_offset_fast: out.nreads_before_compact_offset_fast,
            nreads_before_compact_offset_slow: out.nreads_before_compact_offset_slow,
            nreads_after_compact_offset_fast: out.nreads_after_compact_offset_fast,
            nreads_after_compact_offset_slow: out.nreads_after_compact_offset_slow,
            bytes_read_before_compact_offset_fast: out.bytes_read_before_compact_offset_fast,
            bytes_read_before_compact_offset_slow: out.bytes_read_before_compact_offset_slow,
            bytes_read_after_compact_offset_fast: out.bytes_read_after_compact_offset_fast,
            bytes_read_after_compact_offset_slow: out.bytes_read_after_compact_offset_slow,
            compacted_nodes_in_fast: out.compacted_nodes_in_fast,
            compacted_nodes_in_slow: out.compacted_nodes_in_slow,
            nodes_copied_fast_to_fast_for_fast: out.nodes_copied_fast_to_fast_for_fast,
            nodes_copied_fast_to_fast_for_slow: out.nodes_copied_fast_to_fast_for_slow,
            nodes_copied_slow_to_fast_for_slow: out.nodes_copied_slow_to_fast_for_slow,
            compacted_bytes_in_fast: out.compacted_bytes_in_fast,
            compacted_bytes_in_slow: out.compacted_bytes_in_slow,
            bytes_copied_slow_to_fast_for_slow: out.bytes_copied_slow_to_fast_for_slow,
            nodes_updated_expire: out.nodes_updated_expire,
            nreads_expire: out.nreads_expire,
        })
    }
}

impl Drop for TriedbStatsReader {
    fn drop(&mut self) {
        unsafe { ffi::triedb_stats_close(self.ptr) };
    }
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

    /// The on-disk dual-DB migration phase. Phases only change offline
    /// (monad-mpt with readers and the daemon stopped), so the answer is
    /// fixed for the lifetime of the handle. Cheap and safe on a read-only
    /// handle while execution writes.
    pub fn migration_phase(&self) -> MigrationPhase {
        MigrationPhase::from_code(unsafe { ffi::triedb_migration_phase(self.db_ptr) })
    }

    /// Storage-pool disk capacity and usage in bytes. Safe on a read-only
    /// handle while execution writes.
    pub fn storage_stats(&self) -> StorageStats {
        let mut out = ffi::triedb_storage_stats {
            disk_capacity_bytes: 0,
            disk_used_bytes: 0,
        };
        unsafe { ffi::triedb_storage_stats_read(self.db_ptr, &mut out) };
        StorageStats {
            disk_capacity_bytes: out.disk_capacity_bytes,
            disk_used_bytes: out.disk_used_bytes,
        }
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

    /// Earliest version on file in the primary timeline. Versions below it
    /// are only on file in the secondary (when one is active); on an archive
    /// node after the offline promote that is the frozen slot history.
    pub fn primary_earliest_version(&self) -> Option<u64> {
        parse_triedb_block_num(unsafe { ffi::triedb_primary_earliest_version(self.db_ptr) })
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

#[cfg(test)]
mod migration_phase_tests {
    use super::MigrationPhase;

    #[test]
    fn from_code_maps_known_and_unknown() {
        assert_eq!(MigrationPhase::from_code(0), MigrationPhase::Legacy);
        assert_eq!(MigrationPhase::from_code(1), MigrationPhase::DualTimeline);
        assert_eq!(MigrationPhase::from_code(2), MigrationPhase::PageEncoded);
        assert_eq!(MigrationPhase::from_code(3), MigrationPhase::Promoted);
        // Unexpected codes fall back to Legacy rather than panicking in a
        // monitoring path.
        assert_eq!(MigrationPhase::from_code(4), MigrationPhase::Legacy);
        assert_eq!(MigrationPhase::from_code(255), MigrationPhase::Legacy);
    }
}

#[cfg(test)]
mod update_stats_tests {
    use std::{fs, path::PathBuf};

    use super::{TriedbStatsReader, UpdateStats};

    const MAGIC: u64 = 0x4d4f_4e41_4453_5453;
    const FORMAT_VERSION: u32 = 1;
    const FIELDS: usize = 20;
    const PAYLOAD_SIZE: u32 = (FIELDS * 8) as u32;

    fn sidecar_path(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("monad_db_stats_rs_{}_{name}", std::process::id()))
    }

    struct RemoveOnDrop(PathBuf);

    impl Drop for RemoveOnDrop {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.0);
        }
    }

    fn write_sidecar(path: &PathBuf, seq: u32, values: impl Fn(usize) -> u64) {
        let mut bytes = Vec::with_capacity(24 + FIELDS * 8);
        bytes.extend_from_slice(&MAGIC.to_ne_bytes());
        bytes.extend_from_slice(&FORMAT_VERSION.to_ne_bytes());
        bytes.extend_from_slice(&PAYLOAD_SIZE.to_ne_bytes());
        bytes.extend_from_slice(&seq.to_ne_bytes());
        bytes.extend_from_slice(&0u32.to_ne_bytes());
        for i in 0..FIELDS {
            bytes.extend_from_slice(&values(i).to_ne_bytes());
        }
        fs::write(path, &bytes).unwrap();
    }

    // The state a scraper hits when it samples mid-publish: the reader is open
    // and healthy, and the answer is simply "not this time".
    #[test]
    fn update_stats_is_none_while_a_publish_is_in_flight() {
        let path = sidecar_path("publish_in_flight");
        let _cleanup = RemoveOnDrop(path.clone());
        write_sidecar(&path, 1, |_| 7);

        let reader = TriedbStatsReader::try_new(&path).expect("sidecar should open");
        assert!(reader.update_stats().is_none());
    }

    #[test]
    fn try_new_returns_none_when_the_sidecar_is_absent() {
        let path = sidecar_path("absent");
        let _ = fs::remove_file(&path);
        assert!(TriedbStatsReader::try_new(&path).is_none());
    }

    #[test]
    fn every_counter_reads_back_from_its_own_field() {
        // Field n on the wire carries n + 1, so a counter wired to the wrong
        // offset reports a neighbour's value instead of its own.
        assert_eq!(
            std::mem::size_of::<super::UpdateStats>(),
            FIELDS * 8,
            "a counter was added without extending this fixture"
        );

        let path = sidecar_path("field_mapping");
        let _cleanup = RemoveOnDrop(path.clone());
        write_sidecar(&path, 2, |i| i as u64 + 1);

        let reader = TriedbStatsReader::try_new(&path).expect("sidecar should open");
        let stats = reader.update_stats().expect("counters should be present");

        assert_eq!(
            stats,
            UpdateStats {
                nodes_created_or_updated: 1,
                nreads_compaction: 2,
                nreads_before_compact_offset_fast: 3,
                nreads_before_compact_offset_slow: 4,
                nreads_after_compact_offset_fast: 5,
                nreads_after_compact_offset_slow: 6,
                bytes_read_before_compact_offset_fast: 7,
                bytes_read_before_compact_offset_slow: 8,
                bytes_read_after_compact_offset_fast: 9,
                bytes_read_after_compact_offset_slow: 10,
                compacted_nodes_in_fast: 11,
                compacted_nodes_in_slow: 12,
                nodes_copied_fast_to_fast_for_fast: 13,
                nodes_copied_fast_to_fast_for_slow: 14,
                nodes_copied_slow_to_fast_for_slow: 15,
                compacted_bytes_in_fast: 16,
                compacted_bytes_in_slow: 17,
                bytes_copied_slow_to_fast_for_slow: 18,
                nodes_updated_expire: 19,
                nreads_expire: 20,
            }
        );
    }
}
